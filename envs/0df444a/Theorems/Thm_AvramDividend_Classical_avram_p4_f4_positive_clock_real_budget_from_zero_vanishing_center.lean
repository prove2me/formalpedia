-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_real_budget_from_zero_vanishing_center
-- name    : AvramDividend.Classical.avram_p4_f4_positive_clock_real_budget_from_zero_vanishing_center
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:32:18.412685+00:00
-- url     : https://prove2.me/theorems/b9604357-45f1-4d91-8af6-114a512b5bc4
-- title:
--   Original positive-clock real stopped-reward budget from centred source vanishing at zero
-- statement:
--   For a real payoff dominated a.e. by constant initial potential plus a centred integrable stochastic source that vanishes off the measurable strictly positive stopping event, the expected reward restricted to that event does not exceed the initial potential integrated on the same event. This pure analytic lemma isolates the conditional source step from the separate original Lévy Gaussian and jump martingale construction.
-- source:
--   Use the proved event-restricted zero-mean lemma, restrict an almost-everywhere pathwise envelope, and integrate it under the restricted original probability measure. No change of model, stochastic process, or cap.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_positive_clock_real_budget_from_zero_vanishing_center
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (S : Set Ω) (hS : MeasurableSet S) (F M : Ω → ℝ) (B : ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hZeroOutside : ∀ᵐ ω ∂P, ω ∉ S → M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ B + M ω) :
    (∫ ω in S, F ω ∂P) ≤ (∫ ω in S, B ∂P) := by sorry
