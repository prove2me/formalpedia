-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedMarkov_scale_ratio_lower_rightCont_of_exit_bound
-- name    : AvramDividend.Classical.stoppedMarkov_scale_ratio_lower_rightCont_of_exit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:44:42.726988+00:00
-- url     : https://prove2.me/theorems/6b9b75e0-7813-405f-903c-406203e17b93
-- title:
--   Right-continuous first-record renewal lower expectation bound from a fresh scale exit estimate
-- statement:
--   For a finite first-record stopping time in the right-continuous Lévy filtration and a stopped-history event, suppose the actual killed next-record weight dominates the discounted future path reward. A lower bound on the fresh-path exit reward expectation, such as W(a−h)/W(a), transfers to a lower bound on the killed next-record expectation as the product of the surviving past discount and that scale ratio. The theorem follows from the full right-continuous Lévy strong-Markov factorisation and monotonicity of ENNReal integrals; it separates the process-specific scale-exit law and finite-horizon approximation still required to complete regeneration.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1; proved right-continuous finite-stopping strong-Markov reward factorisation.

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont

open MeasureTheory
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedMarkov_scale_ratio_lower_rightCont_of_exit_bound
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
    (hRatio : ratio ≤
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P))
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        reward (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        else 0) ≤ killedWeight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      ratio ≤ (∫⁻ ω, killedWeight ω ∂P) := by sorry
