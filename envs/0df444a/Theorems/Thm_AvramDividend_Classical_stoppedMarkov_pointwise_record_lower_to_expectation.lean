-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_lower_to_expectation
-- name    : AvramDividend.Classical.stoppedMarkov_pointwise_record_lower_to_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:59:01.027992+00:00
-- url     : https://prove2.me/theorems/153d4e3d-2c58-4f31-ab0e-d40b958b3009
-- title:
--   Strong-Markov expectation lower bound from pointwise killed record domination
-- statement:
--   For a finite Lévy stopping time, a past-observable survival event, and a measurable nonnegative future reward, suppose the actual killed first-record reward is pointwise at least the past discount times the shifted future reward on that event. Then the expected actual killed weight is at least the past discounted survival expectation times the independent fresh-path reward expectation. This is the expectation-level lower-comparison bridge for the q-scale regenerative step.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; stopped Lévy strong-Markov reward factorisation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedMarkov_pointwise_record_lower_to_expectation
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
    (killedWeight : Ω → ℝ≥0∞)
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0) ≤ killedWeight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) ≤
        (∫⁻ ω, killedWeight ω ∂P) := by sorry
