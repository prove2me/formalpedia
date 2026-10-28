-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_lower_to_expectation_rightCont
-- name    : AvramDividend.Classical.stoppedMarkov_pointwise_record_lower_to_expectation_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:45:58.242239+00:00
-- url     : https://prove2.me/theorems/fc1e1b94-246c-46ea-854d-8e943e546af2
-- title:
--   Killed first-record reward lower bound from strong Markov at a right-continuous stopping time
-- statement:
--   For a finite stopping time relative to the right-continuous Lévy filtration, a measurable past event and a measurable nonnegative reward of future increments, assume the killed next-record payment dominates the product of past discount and future shifted reward pointwise. Then the expected killed payment is at least the expected past discounted surviving mass multiplied by the independent expected fresh-path reward. This is the missing right-continuous lower expectation counterpart to the already proved upper one, and matches the available first-upcrossing stopping-time theorem.
-- source:
--   Direct consequence of the remotely Proved levy_finiteStopping_killedDiscount_futureReward_factor_rightCont and monotonicity of the nonnegative Lebesgue integral; Avram, Palmowski and Pistorius (2007), Proposition 1.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedMarkov_pointwise_record_lower_to_expectation_rightCont
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
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0) ≤ killedWeight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) ≤
        (∫⁻ ω, killedWeight ω ∂P) := by sorry
