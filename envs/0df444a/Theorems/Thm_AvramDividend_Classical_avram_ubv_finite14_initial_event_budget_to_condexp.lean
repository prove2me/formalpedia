-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
-- name    : AvramDividend.Classical.avram_ubv_finite14_initial_event_budget_to_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:43:52.116758+00:00
-- url     : https://prove2.me/theorems/9904a1e6-810e-4291-8427-31a78ec640d6
-- title:
--   Initial-filtration eventwise budget implies conditional expectation bound
-- statement:
--   If the original stopped reward is integrable and its integral over every initial-filtration event is at most b times that event's probability, its conditional expectation given the initial filtration is at most b almost surely. This is the exact conversion step for Open original finite-cap Gaussian source c31f81c8 and existing Proved initial-event martingale budget 12ae9b2d.
-- source:
--   Finite-cap UBV original stopped Gaussian event-budget-to-condExp bridge; intended direct import into root-connected c31f81c8.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite14_initial_event_budget_to_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (F : Ω → ℝ) (b : ℝ) (hFI : Integrable F P)
    (hBudget : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by sorry
