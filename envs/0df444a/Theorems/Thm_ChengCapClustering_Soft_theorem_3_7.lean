-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_theorem_3_7
-- name    : ChengCapClustering.Soft.theorem_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:18.907057+00:00
-- url     : https://prove2.me/theorems/9a635b66-0e9d-4458-be7a-91a5585edf6b
-- title:
--   Theorem 3.7 — framework theorem: at most $K$ centers and cost $\le(\beta-(\beta-1)\varepsilon+4\beta\eta)\,\mathrm{cost}(S^*)$ for every admissible reference $S^*$, $\beta=u+2^zv$
-- statement:
--   Fix $D\ge1$, $z\ge1$, $\varepsilon\in(0,1]$, $\eta\in(0,1/10]$, $u\ge1$ and $v\ge0$, and let $\beta=u+2^zv$. There is a deterministic algorithm whose input is an instance with soft capacities such that $P\cup F$ has doubling dimension at most $D$, together with a block partition in which every block is $(u,v)$-movable. It outputs a soft solution with at most $K$ centers whose cost is at most $(\beta-(\beta-1)\varepsilon+4\beta\eta)\cdot\mathrm{cost}(S^*)$ for every soft solution $S^*$ with at most $k$ centers such that $A\le(1+\eta)\,\mathrm{cost}(S^*)$. Its running time is polynomial in $n$, $|F|$ and $\log\Delta(P\cup F)$, with a degree that depends on $D,z,\varepsilon,\eta$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: running time polynomial in n, |F| and log Δ(P ∪ F), degree depending on D, z, ε, η → a degree deg chosen from D, z, ε, η before u, v, and a constant C: at most C (n+m+2)^deg (2 + log₂ Δ)^deg steps, Δ the aspect ratio of the listed points of P ∪ F; reason: the stated form of polynomial time
--   - encoding: an instance with soft capacities (Definition 2.1, k < n, a solution with ≤ k centers exists) → clients p : Fin n → V, locations an injective list f : Fin m → V with m > 0, 0 < k < n, 0 < U, n ≤ kU; block partition given by block labels and representative indices into f; reason: the standing assumptions of §2 as hypotheses; F nonempty is implied by the existence of a solution
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Theorem 3.7, printed p. 12 / PDF p. 14

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering

open MinSumDimRed.Doubling

universe u

namespace ChengCapClustering.Soft

/-- Theorem 3.7 (Framework theorem), printed p. 12 / PDF p. 14. Fix `D ≥ 1`, `z ≥ 1`, `ε ∈ (0, 1]`,
`η ∈ (0, 1/10]`, `u ≥ 1`, `v ≥ 0`, and let `β = u + 2^z v`. One deterministic program takes a
soft-capacity instance with `P ∪ F` of doubling dimension at most `D` and a block partition whose
blocks are all `(u, v)`-movable, and outputs a soft solution with at most `K` centers whose cost is
at most `(β − (β − 1)ε + 4βη) cost(S*)` for every soft solution `S*` with at most `k` centers and
`A ≤ (1 + η) cost(S*)`; its running time is polynomial in `n`, `|F|` and `log Δ(P ∪ F)`, with a degree
`deg` that depends only on `D`, `z`, `ε`, `η`. -/
theorem theorem_3_7 :
    ∀ D z ε η : ℝ, 1 ≤ D → 1 ≤ z → 0 < ε → ε ≤ 1 → 0 < η → η ≤ 1 / 10 →
      ∃ deg : ℕ, ∀ u v : ℝ, 1 ≤ u → 0 ≤ v →
      ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
        ∀ (V : Type u) [MetricSpace V] (n m k U : ℕ) (p : Fin n → V) (f : Fin m → V)
          (mb : ℕ) (blk : Fin n → Fin mb) (repIdx : Fin mb → Fin m),
          Function.Injective f → 0 < k → k < n → 0 < U → n ≤ k * U → 0 < m →
          IsDoublingWith (Set.range p ∪ Set.range f) D →
          IsBlockPartition k U (Set.range f) (⟨mb, blk, f ∘ repIdx⟩ : BlockPartition V n) →
          (∀ i, IsMovable z u v (Set.range f)
            ((⟨mb, blk, f ∘ repIdx⟩ : BlockPartition V n).members i) p (f (repIdx i))) →
          HaltsWithin prog
            ([(n : ℤ), (m : ℤ), (k : ℤ), (U : ℤ), (mb : ℤ)] ++
              List.ofFn (fun q => ((blk q : ℕ) : ℤ)) ++ List.ofFn fun i => ((repIdx i : ℕ) : ℤ))
            ([z, ε, η, u, v] ++ distanceList (instancePoints p f))
            ((C : ℝ) * ((n + m + 2 : ℕ) : ℝ) ^ deg *
              (2 + Real.logb 2 (aspectRatio (instancePoints p f))) ^ deg)
            (fun s => ∃ S : IdxSolution n m,
              IsSoftSolution (Set.range f) U (numOpenK k ε) (S.toSoft f) ∧
              (∀ Sstar : SoftSolution V n, IsSoftSolution (Set.range f) U k Sstar →
                (⟨mb, blk, f ∘ repIdx⟩ : BlockPartition V n).totalCost z p ≤
                  (1 + η) * Sstar.cost z p →
                (S.toSoft f).cost z p ≤
                  (u + (2 : ℝ) ^ z * v - (u + (2 : ℝ) ^ z * v - 1) * ε +
                    4 * (u + (2 : ℝ) ^ z * v) * η) * Sstar.cost z p) ∧
              OutputIs s S.encode []) := by sorry

end ChengCapClustering.Soft
