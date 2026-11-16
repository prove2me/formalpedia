-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_prob_twojump_le_half_second_factorial_mean_20261115
-- name    : AvramDividend.Classical.avram_a25_prob_twojump_le_half_second_factorial_mean_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:03:37.41071+00:00
-- url     : https://prove2.me/theorems/e5b85a69-b8bd-474e-94b7-9a1efb3da216
-- title:
--   Probability of at least two counting events bounded by half the second factorial expectation
-- statement:
--   For an integrable second falling factorial of a measurable natural count on a probability space, the probability of two or more points is at most half its second factorial moment. This is the direct Markov bound 1_{K≥2} ≤ K(K−1)/2 integrated under the original measure. Applying the existing physical negative-Borel jump count second factorial source theorem gives a uniform O((ν(B)T)^2) collision bound, the essential source ingredient for a Bernoulli-cell Poisson characteristic-function approximation.
-- source:
--   Pinned Mathlib MeasureTheory.integral_mono_ae, integral_indicator_one, integral_div, and submitted pointwise 20261115 theorem.

import Mathlib
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a25_prob_twojump_le_half_second_factorial_mean_20261115
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (hSecond : Integrable
      (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P) :
    (P {ω | 2 ≤ K ω}).toReal ≤
      (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) / 2 := by sorry
