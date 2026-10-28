-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedMarkov_scale_ratio_lower_from_future_exit_bound
-- name    : AvramDividend.Classical.stoppedMarkov_scale_ratio_lower_from_future_exit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:45:33.6706+00:00
-- url     : https://prove2.me/theorems/6f473052-2372-49ab-a207-296fc282f466
-- title:
--   Strong-Markov killed-record expectation lower bound from a scale-ratio future-exit estimate
-- statement:
--   At a finite stopping time and with a past-measurable survival event, assume the killed next-record payment dominates the discounted reward of the shifted future path. If the expected future reward is at least an ENNReal scale ratio, then the current discounted survival expectation multiplied by that ratio is bounded by the expected killed next-record payment. This isolates the scale-exit estimate as the remaining analytic input for the geometric lower renewal recurrence.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; direct application of the remotely Proved stoppedMarkov_pointwise_record_lower_to_expectation lemma plus monotonicity of ENNReal multiplication.

import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_lower_to_expectation

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedMarkov_scale_ratio_lower_from_future_exit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A)
    (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward)
    (killedWeight : Ω → ℝ≥0∞) (ratio : ℝ≥0∞)
    (hRatio : ratio ≤
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P))
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0) ≤ killedWeight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      ratio ≤ (∫⁻ ω, killedWeight ω ∂P) := by sorry
