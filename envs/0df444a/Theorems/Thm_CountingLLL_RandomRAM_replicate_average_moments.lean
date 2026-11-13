-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_replicate_average_moments
-- name    : CountingLLL.RandomRAM.replicate_average_moments
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:26:47.664218+00:00
-- url     : https://prove2.me/theorems/77da3c3f-bed6-4137-b691-750ef0259140
-- title:
--   Moments of the averaged randomized marginal estimator
-- statement:
--   Let L be a positive integer and let R_1,...,R_L be independent square-integrable real random variables, each with mean r and variance at most 3p. Then X=1-(R_1+...+R_L)/L is square-integrable, has mean 1-r, and has variance at most 3p/L. This is the independent-replicate averaging step in the randomized counting proof, once the single-invocation moments from Lemma 5.6 are available.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Theorem 1.3, Section 5.3, PDF pp.20-21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.replicate_average_moments {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (L : ℕ) (hL : 0 < L) (R : Fin L → Ω → ℝ) (r p : ℝ)
    (hind : iIndepFun R μ) (hL2 : ∀ j, MemLp (R j) 2 μ)
    (hmean : ∀ j, (∫ ω, R j ω ∂μ) = r)
    (hvar : ∀ j, variance (R j) μ ≤ 3 * p) :
    let X : Ω → ℝ := fun ω => 1 - (L : ℝ)⁻¹ * ∑ j, R j ω
    MemLp X 2 μ ∧ (∫ ω, X ω ∂μ) = 1 - r ∧ variance X μ ≤ 3 * p / L := by sorry
