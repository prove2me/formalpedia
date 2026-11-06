-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn20_stopped_if_integral_eq_selected_setIntegral
-- name    : AvramDividend.Classical.avram_bv_env3_turn20_stopped_if_integral_eq_selected_setIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:50:22.366481+00:00
-- url     : https://prove2.me/theorems/87496953-f30e-46d5-8090-39736f456fd3
-- title:
--   Stopped physical-grid if-mask equals predictable selected set integral
-- statement:
--   An integrable or arbitrary real-valued original physical-grid source increment, masked by the measurable event i<k(omega), has the same expectation as its integral on the selected event. This is the exact equality needed to connect predictable conditional expectation to the previously accepted stopped signed-grid budget.
-- source:
--   Pinned Mathlib MeasureTheory.integral_indicator; used with the original predictable source condExp mean-zero lemma BV-ENV3 turn19 and selected stopped-grid mean-zero budget turn10.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn20_stopped_if_integral_eq_selected_setIntegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (k : Ω → ℕ) (hk : Measurable k)
    (i : ℕ) (M : Ω → ℝ) :
    (∫ ω, (if i < k ω then M ω else 0) ∂P) =
      (∫ ω in {ω : Ω | i < k ω}, M ω ∂P) := by sorry
