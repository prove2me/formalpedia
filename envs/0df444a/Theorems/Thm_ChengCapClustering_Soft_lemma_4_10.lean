-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_4_10
-- name    : ChengCapClustering.Soft.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:53:08.910404+00:00
-- url     : https://prove2.me/theorems/3435f7c6-c89a-467e-ac43-368ddc5fb5a0
-- title:
--   Lemma 4.10 — dynamic program: a minimum-cost feasible network solution in time $(2n+1)^{O(M)}\mathrm{poly}(|X|,H)$
-- statement:
--   In the setting of §4.3 ($X=P\cup F$ of doubling dimension at most $D$ with minimum distance $2$, a block partition, $u\ge1$, $v\ge0$, a hierarchical decomposition $D$ and portals with spacing $\lambda\in(0,1]$), a feasible network solution of minimum cost $\Phi$, if one exists, can be computed in time $(2n+1)^{O(M)}\cdot\mathrm{poly}(|X|,H)$, where $M=\lceil(4/\lambda)^D\rceil$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: "if one exists" → the program always halts within the bound; it writes flag 1 and a minimum-cost feasible network solution when one exists, and flag 0 when none exists; reason: the dynamic program detects infeasibility (an empty root table); the stronger reading
--   - reading: time (2n+1)^{O(M)} · poly(|X|, H) → one program and one absolute constant C for all D, z, ε, u, v, λ: at most C (2n+1)^{C M} (L+2)^C steps, L the input length; reason: L is polynomial in |X| and H plus at most 3n client and block entries, absorbed by (2n+1)^{O(M)}
--   - encoding: the instance, block partition, decomposition and network N_D → point-indexed instance (X injective, clients by point index, F an index set), block labels and representative indices, decomposition labels and a valid portal system as input; the solution as a rescued-set indicator and a flow list; reason: input and output layouts
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 4.10, printed p. 18 / PDF p. 20

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Network

open MinSumDimRed.Doubling

universe u

namespace ChengCapClustering.Soft

/-- Lemma 4.10 (Dynamic program), printed p. 18 / PDF p. 20. One program computes a feasible network
solution of minimum cost `Φ` whenever one exists (output flag `1` followed by the solution) and
reports `0` otherwise, in time `(2n + 1)^{O(M)} · poly(|X|, H)` with `M = ⌈(4/λ)^D⌉`. The input is
the point-indexed instance with its block partition, the decomposition `D` and its portal system;
the time bound is stated as `C (2n+1)^{C M} (L + 2)^C` for the input length `L` (which is polynomial
in `|X|` and `H`, plus the `n + m ≤ 3n` client and block entries). -/
theorem lemma_4_10 :
    ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
      ∀ (V : Type u) [MetricSpace V] (D z ε u v lam : ℝ) (N n k U m : ℕ) (x : Fin N → V)
        (cl : Fin n → Fin N) (Floc : Finset (Fin N)) (blk : Fin n → Fin m)
        (repIdx : Fin m → Fin N) (Dec : HierDecomp N) (P : PortalSystem N Dec.H),
        Function.Injective x → (∀ i, (∃ q, cl q = i) ∨ i ∈ Floc) →
        0 < k → k < n → 0 < U → n ≤ k * U → 1 ≤ z → 0 < ε → ε ≤ 1 → 1 ≤ u → 0 ≤ v →
        0 < lam → lam ≤ 1 → IsDoublingWith (Set.range x) D → MinDistTwo x →
        Dec.IsValid x → P.IsValid x Dec lam →
        IsBlockPartition k U (x '' ↑Floc) (⟨m, blk, x ∘ repIdx⟩ : BlockPartition V n) →
        let B : BlockPartition V n := ⟨m, blk, x ∘ repIdx⟩
        let K := numOpenK k ε
        let ints := encodePointInstance k U cl Floc blk repIdx ++ Dec.encode ++ P.encode
        let reals := [z, ε, u, v, lam] ++ distanceList x
        let M := ⌈((4 : ℝ) / lam) ^ D⌉₊
        HaltsWithin prog ints reals
          ((C : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ^ (C * M) *
            ((ints.length + reals.length + 2 : ℕ) : ℝ) ^ C)
          (fun s =>
            ((∃ S : NetSolution N Dec.H m, IsFeasibleNetSolution x (x '' ↑Floc) U K Dec P B S) →
              ∃ (R : Finset (Fin m)) (L : List (NetVertex N Dec.H × NetVertex N Dec.H × ℕ)),
                IsFeasibleNetSolution x (x '' ↑Floc) U K Dec P B ⟨R, flowOfList L⟩ ∧
                (∀ S' : NetSolution N Dec.H m,
                  IsFeasibleNetSolution x (x '' ↑Floc) U K Dec P B S' →
                  netCost x (x ∘ cl) z u v lam Dec B ⟨R, flowOfList L⟩ ≤
                    netCost x (x ∘ cl) z u v lam Dec B S') ∧
                OutputIs s (1 :: encodeNetSolution R L) []) ∧
            ((¬ ∃ S : NetSolution N Dec.H m, IsFeasibleNetSolution x (x '' ↑Floc) U K Dec P B S) →
              OutputIs s [0] [])) := by sorry

end ChengCapClustering.Soft
