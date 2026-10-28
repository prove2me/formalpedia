-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
-- name    : AvramDividend.Classical.levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:59:16.098282+00:00
-- url     : https://prove2.me/theorems/f4c6b616-f9ee-4440-b6a9-58690bc65480
-- title:
--   Killed discounted future reward factorisation at right-continuous Lévy stopping times
-- statement:
--   Let a finite random clock be a stopping time of the canonical right-continuous filtration, with a measurable stopped-history event. The expected discounted reward of its shifted Lévy future path on that event factors as the stopped-history discounted mass times the independent original-path expected reward. The result transports the already proved general finite-stopping-time reward factorisation through the proved right-continuous Lévy-process construction, and is directly reusable for killed first-record renewal estimates.
-- source:
--   Use the proved right-continuous path-preserving Lévy process and the existing finite-stopping discounted future-reward factorisation, then rewrite identical paths.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor

open MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
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
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
      (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by sorry
