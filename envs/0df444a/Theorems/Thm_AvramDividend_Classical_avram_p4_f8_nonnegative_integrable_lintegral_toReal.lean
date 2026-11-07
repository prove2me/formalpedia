-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f8_nonnegative_integrable_lintegral_toReal
-- name    : AvramDividend.Classical.avram_p4_f8_nonnegative_integrable_lintegral_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:37:00.542591+00:00
-- url     : https://prove2.me/theorems/70d4d80f-10fe-4035-9c81-5d255562235e
-- title:
--   Positive integrable real expectation equals the real part of its ENNReal lintegral
-- statement:
--   For an integrable everywhere nonnegative real-valued function, converting its ENNReal-ofReal lintegral back to real recovers the ordinary Bochner integral. This deterministic interface transports the source-backed real Dynkin inequality to Prove2Me's extended-real stopped expectation.

import Mathlib
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f8_nonnegative_integrable_lintegral_toReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂P).toReal = ∫ ω, f ω ∂P := by sorry
