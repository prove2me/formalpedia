-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_positive_event_budget_to_centred_masked_witness
-- name    : AvramDividend.Classical.avram_f6_positive_event_budget_to_centred_masked_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T15:50:20.676525+00:00
-- url     : https://prove2.me/theorems/34d4415a-a241-4383-bfc8-3d1e584ac1c1
-- title:
--   A positive-mass event expected budget gives an event-supported centred signed witness
-- statement:
--   For any probability space, any measurable event of positive probability and integrable real reward f, an upper bound on its event-restricted expectation by b times event probability yields a centred integrable martingale-candidate M supported only on that event, and a nonpositive signed drift G, such that f ≤ b+M+G on the event. Explicit construction from the conditional mean, including no source-changing truncation.
-- source:
--   Elementary conditional-event centering identity, original Avram F6 zero/positive clock masked expected-budget bridge.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_positive_event_budget_to_centred_masked_witness
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (hPos : 0 < (P A).toReal)
    (f : Ω → ℝ) (hf : Integrable f P) (b : ℝ)
    (hBudget : (∫ ω in A, f ω ∂P) ≤ b * (P A).toReal) :
    ∃ M G : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ ω, ω ∉ A → M ω = 0) ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, ω ∈ A → f ω ≤ b + M ω + G ω) := by sorry
