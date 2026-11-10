-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_4_11
-- name    : ChengCapClustering.Soft.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:53:08.926505+00:00
-- url     : https://prove2.me/theorems/a3439c3d-4f3e-4654-b925-4c13f1d8e320
-- title:
--   Lemma 4.11 — from a feasible network solution to a soft solution with at most $K$ centers and cost $\le A+\Phi(R,f)$, in polynomial time
-- statement:
--   In the setting of §4.3, suppose that every block is $(u,v)$-movable. Given a feasible network solution $(R,f)$, one can compute in polynomial time a soft solution with at most $K=k+\lfloor\varepsilon k\rfloor$ centers at locations in $F$ whose cost is at most $A+\Phi(R,f)$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: in polynomial time → one program and one absolute constant C: at most C (L+2)^C steps, L the input length; reason: the strongest reading of the polynomial bound
--   - encoding: the instance, block partition, network and (R, f) → point-indexed instance, block labels and representative indices, decomposition, portal system, and (R, f) with f given by a list of arc entries; the output soft solution by location indices into X (which must lie in F); reason: input and output layouts
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 4.11, printed p. 18 / PDF p. 20

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Network

open MinSumDimRed.Doubling

universe u

namespace ChengCapClustering.Soft

/-- Lemma 4.11 (From network solutions to clusterings), printed p. 18 / PDF p. 20. If every block is
`(u, v)`-movable, then from a feasible network solution `(R, f)` one program computes, in polynomial
time, a soft solution with at most `K` centers at locations in `F` whose cost is at most `A + Φ(R, f)`.
The input is the point-indexed instance with its block partition, the decomposition, its portal
system and `(R, f)` (`f` given by a list of arc entries). -/
theorem lemma_4_11 :
    ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
      ∀ (V : Type u) [MetricSpace V] (D z ε u v lam : ℝ) (N n k U m : ℕ) (x : Fin N → V)
        (cl : Fin n → Fin N) (Floc : Finset (Fin N)) (blk : Fin n → Fin m)
        (repIdx : Fin m → Fin N) (Dec : HierDecomp N) (P : PortalSystem N Dec.H)
        (R : Finset (Fin m)) (L : List (NetVertex N Dec.H × NetVertex N Dec.H × ℕ)),
        Function.Injective x → (∀ i, (∃ q, cl q = i) ∨ i ∈ Floc) →
        0 < k → k < n → 0 < U → n ≤ k * U → 1 ≤ z → 0 < ε → ε ≤ 1 → 1 ≤ u → 0 ≤ v →
        0 < lam → lam ≤ 1 → IsDoublingWith (Set.range x) D → MinDistTwo x →
        Dec.IsValid x → P.IsValid x Dec lam →
        IsBlockPartition k U (x '' ↑Floc) (⟨m, blk, x ∘ repIdx⟩ : BlockPartition V n) →
        (∀ i, IsMovable z u v (x '' ↑Floc)
          ((⟨m, blk, x ∘ repIdx⟩ : BlockPartition V n).members i) (x ∘ cl) (x (repIdx i))) →
        IsFeasibleNetSolution x (x '' ↑Floc) U (numOpenK k ε) Dec P
          (⟨m, blk, x ∘ repIdx⟩ : BlockPartition V n) ⟨R, flowOfList L⟩ →
        let B : BlockPartition V n := ⟨m, blk, x ∘ repIdx⟩
        let ints := encodePointInstance k U cl Floc blk repIdx ++ Dec.encode ++ P.encode ++
          encodeNetSolution R L
        let reals := [z, ε, u, v, lam] ++ distanceList x
        HaltsWithin prog ints reals
          ((C : ℝ) * ((ints.length + reals.length + 2 : ℕ) : ℝ) ^ C)
          (fun s => ∃ S : IdxSolution n N,
            (∀ j, S.locIdx j ∈ Floc) ∧
            IsSoftSolution (x '' ↑Floc) U (numOpenK k ε) (S.toSoft x) ∧
            (S.toSoft x).cost z (x ∘ cl) ≤
              B.totalCost z (x ∘ cl) + netCost x (x ∘ cl) z u v lam Dec B ⟨R, flowOfList L⟩ ∧
            OutputIs s S.encode []) := by sorry

end ChengCapClustering.Soft
