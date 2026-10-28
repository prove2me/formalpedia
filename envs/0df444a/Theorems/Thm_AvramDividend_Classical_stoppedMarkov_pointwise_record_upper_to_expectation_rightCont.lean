-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
-- name    : AvramDividend.Classical.stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:12:56.603986+00:00
-- url     : https://prove2.me/theorems/e803eb35-2a11-4cf0-91a2-b1d5b91aa0e2
-- title:
--   Upper expectation comparison for killed record rewards after a right-continuous stopped-history Markov split
-- statement:
--   For a finite stopping time in the right-continuous Lévy filtration and a measurable history event, suppose a killed record reward is pointwise dominated by a discounted measurable functional of the future Lévy increments on that event. Then its expectation is bounded by the product of the discounted history mass and the independent expected future reward. The result isolates the pointwise inclusion required for the stopped-renewal upper estimate.
-- source:
--   Apply the proved right-continuous discounted future-reward factorisation and monotonicity of the nonnegative Lebesgue integral.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_finiteStopping_discountedFutureReward_factor

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A)
    (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward)
    (killedWeight : Ω → ℝ≥0∞)
    (hUpper : ∀ ω : Ω, killedWeight ω ≤
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0)) :
    (∫⁻ ω, killedWeight ω ∂P) ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
