-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor
-- name    : AvramDividend.Classical.levy_finiteStopping_killedDiscount_futureReward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:39:15.731705+00:00
-- url     : https://prove2.me/theorems/fee07874-fb60-449b-ae49-72731cade284
-- title:
--   Killed discounted stopping-event weight factors from post-stopping Lévy rewards
-- statement:
--   Given a finite stopping clock and an event observable at that clock, the expected future Lévy reward multiplied by the event indicator and a measurable discount of the stopping time factors into the expected discounted survival indicator and the original-path expected reward. This is the precise strong-Markov factorisation used by the barrier dividend up-exit identity.
-- source:
--   Imports proved finiteStopping_clock_measurable_stoppedSigma 7b726fe4-39eb-44f8-b346-548eb444ff0f and established Lévy stopped-history reward factor b995a471-5065-4673-ba97-d0f13ebfc768. The remaining barrier target 79978d61-9d1f-4b20-b8a5-114797a8e380 needs to instantiate the stopping event and identify pathwise Stieltjes reward.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_killedDiscount_futureReward_factor
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
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  sorry
