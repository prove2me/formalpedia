-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_event_expected_budget_supports_centered_ae
-- name    : AvramDividend.Classical.avram_jump6_B_event_expected_budget_supports_centered_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:45:57.844113+00:00
-- url     : https://prove2.me/theorems/c584627c-f2aa-4cfa-a212-e6c3d4d4d2a5
-- title:
--   Expected event budget yields a supported centred integrable witness including zero-mass events
-- statement:
--   For any probability measure, integrable real F, measurable event A, and real b satisfying the genuine expected bound on A, construct an integrable centred real witness supported on A almost everywhere that dominates F-b almost everywhere on A. Works even when P(A)=0, using the existing Proved positive-mass centering theorem. Does not assume stochastic dividend ledger.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_positive_clock_supported_centered_of_expected
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_event_expected_budget_supports_centered_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (b : ℝ)
    (hBudget : (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal) :
    ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, ω ∉ A → M ω = 0) ∧
      (∀ᵐ ω ∂P, ω ∈ A → F ω ≤ b + M ω) := by sorry
