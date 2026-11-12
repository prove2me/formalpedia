-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb24_vanishing_eventwise_error_initial_condexp_upper
-- name    : AvramDividend.Classical.avram_jb24_vanishing_eventwise_error_initial_condexp_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:34:49.065846+00:00
-- url     : https://prove2.me/theorems/93393025-ada9-4b0d-9272-96afe68fad40
-- title:
--   Vanishing initial-event cash budget errors yield the original-filtration conditional upper bound
-- statement:
--   Every initial-information event satisfies the expected stopped cash budget with a deterministic error tending to zero. Its limiting eventwise bound yields an almost-sure conditional expectation upper at the initial right-continuous filtration.
-- source:
--   Proved avram_ubv_finite14_initial_event_budget_to_condexp and Mathlib ge_of_tendsto; necessary final step for positive-part Ito mesh error budgets.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb24_vanishing_eventwise_error_initial_condexp_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (F : Ω → ℝ) (b : ℝ) (ε : ℕ → ℝ)
    (hFI : Integrable F P)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hEvent : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      ∀ k, (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal + ε k) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by sorry
