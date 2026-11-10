-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_5_1
-- name    : ChengCapClustering.Soft.lemma_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:52:13.288402+00:00
-- url     : https://prove2.me/theorems/787c02e7-b210-499a-a30c-a632df2c6e1b
-- title:
--   Lemma 5.1 — compression: a polynomial-time proxy map with two-sided distortion $1+3\eta_c$ and doubling dimension $D'$
-- statement:
--   Let $Z$ and $Y$ be finite sets in a metric space, where $Z$ has doubling dimension at most $D\ge1$, and let $\eta_c\in(0,1/4]$. One can compute in polynomial time a map $\mu:Y\to Y$ such that for all $x\in Z$ and $y\in Y$, $\mathrm{dist}(x,\mu(y))\le(1+3\eta_c)\mathrm{dist}(x,y)$ and $\mathrm{dist}(x,y)\le(1+3\eta_c)\mathrm{dist}(x,\mu(y))$, and $Z\cup\mu(Y)$ has doubling dimension at most $D'=\log_2(2^{4D}+6(768/\eta_c)^DN)=O((32/\eta_c)^D\log^2(2/\eta_c))$, where $N=(1+11/\eta_c)^{(32/\eta_c)^D+\lceil\log_2(2/\eta_c)\rceil(16/\eta_c)^D}$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: one can compute in polynomial time (D and η_c fixed) → for each D ≥ 1 and η_c ∈ (0, 1/4] one program and a constant C with at most C (|Z| + |Y| + 2)^C steps; reason: D and η_c are fixed parameters of the lemma
--   - reading: D′ = O((32/η_c)^D log²(2/η_c)) → ∃ C, ∀ D ≥ 1, η_c ∈ (0, 1/4], D′ ≤ C (32/η_c)^D (log₂(2/η_c))²; reason: an absolute constant in the O-bound
--   - encoding: finite sets Z, Y; a map μ : Y → Y → injective lists zp, yp; μ as a map of indices of Y written to the output; reason: listing of the sets
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 5.1, printed p. 23 / PDF p. 25

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering

open MinSumDimRed.Doubling

universe u

namespace ChengCapClustering.Soft

/-- Lemma 5.1 (Compression), printed p. 23 / PDF p. 25. For finite sets `Z` and `Y` (injective lists)
in a metric space with `Z` of doubling dimension at most `D ≥ 1` and `η_c ∈ (0, 1/4]`, one program
(for these fixed `D`, `η_c`) computes in polynomial time a map `μ : Y → Y` with
`dist(x, μ(y)) ≤ (1 + 3η_c) dist(x, y)` and `dist(x, y) ≤ (1 + 3η_c) dist(x, μ(y))` for all
`x ∈ Z`, `y ∈ Y`, such that `Z ∪ μ(Y)` has doubling dimension at most
`D′ = log₂(2^{4D} + 6(768/η_c)^D N)`; and `D′ = O((32/η_c)^D log²(2/η_c))`. -/
theorem lemma_5_1 :
    (∀ D ηc : ℝ, 1 ≤ D → 0 < ηc → ηc ≤ 1 / 4 →
      ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
        ∀ (V : Type u) [MetricSpace V] (a b : ℕ) (zp : Fin a → V) (yp : Fin b → V),
          Function.Injective zp → Function.Injective yp → IsDoublingWith (Set.range zp) D →
          HaltsWithin prog [(a : ℤ), (b : ℤ)] ([ηc] ++ distanceList (Fin.append zp yp))
            ((C : ℝ) * ((a + b + 2 : ℕ) : ℝ) ^ C)
            (fun s => ∃ μ : Fin b → Fin b,
              (∀ i j, dist (zp i) (yp (μ j)) ≤ (1 + 3 * ηc) * dist (zp i) (yp j) ∧
                dist (zp i) (yp j) ≤ (1 + 3 * ηc) * dist (zp i) (yp (μ j))) ∧
              IsDoublingWith (Set.range zp ∪ Set.range (yp ∘ μ)) (compressedDim D ηc) ∧
              OutputIs s (List.ofFn fun j => ((μ j : ℕ) : ℤ)) [])) ∧
    ∃ C : ℝ, ∀ D ηc : ℝ, 1 ≤ D → 0 < ηc → ηc ≤ 1 / 4 →
      compressedDim D ηc ≤ C * (32 / ηc) ^ D * Real.logb 2 (2 / ηc) ^ 2 := by sorry

end ChengCapClustering.Soft
