-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedMarkov_scale_ratio_upper_from_future_exit_bound
-- name    : AvramDividend.Classical.stoppedMarkov_scale_ratio_upper_from_future_exit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:45:32.454767+00:00
-- url     : https://prove2.me/theorems/bef9e7e9-794e-4340-9ee8-39ce74a2853d
-- title:
--   Strong-Markov killed-record expectation upper bound from a scale-ratio future-exit estimate
-- statement:
--   At a finite stopping time in the right-continuous Lévy filtration, suppose the killed record payment is pointwise bounded by the past discount times the shifted future exit reward, on a measurable stopped-history event. If the independent expected future reward is at most a specified scale ratio, the killed payment expectation is bounded by the past discounted-survival expectation times that ratio. This provides the expectation-level upper companion to the lower record-renewal interface.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; direct application of the remotely Proved stoppedMarkov_pointwise_record_upper_to_expectation_rightCont lemma and monotonicity of ENNReal multiplication.

import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_upper_to_expectation_rightCont

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedMarkov_scale_ratio_upper_from_future_exit_bound
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
    (killedWeight : Ω → ℝ≥0∞) (ratio : ℝ≥0∞)
    (hRatio :
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) ≤ ratio)
    (hUpper : ∀ ω : Ω, killedWeight ω ≤
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0)) :
    (∫⁻ ω, killedWeight ω ∂P) ≤
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      ratio := by sorry
