-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_weighted_levy_L1_integral_transfer
-- name    : AvramDividend.Classical.avram_wave5_04c_weighted_levy_L1_integral_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:31:04.513208+00:00
-- url     : https://prove2.me/theorems/ebe5edac-21d4-48f5-919a-3f1ffcdc13e0
-- title:
--   Weighted L1 domination transfers signed original Lévy generator integrals quantitatively
-- statement:
--   For Bochner integrable real functions F and G under the actual signed-generator integration measure, an almost everywhere weighted pointwise approximation |F-G|≤epsilon H transfers to a quantitative error on their signed integrals, provided H is integrable. The canonical BV C1 application uses H(y)=1-exp(y) on the original negative Lévy measure, whose integrability is already Proved under genuine bounded variation. Thus no large-negative first moment is imposed.
-- source:
--   integral_sub, abs_integral_le_integral_abs, integral_mono_ae, and integral_const_mul.

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem AvramDividend.Classical.avram_wave5_04c_weighted_levy_L1_integral_transfer
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G H : α → ℝ)
    (hF : MeasureTheory.Integrable F μ)
    (hG : MeasureTheory.Integrable G μ)
    (hH : MeasureTheory.Integrable H μ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbd : ∀ᵐ z ∂μ, |F z - G z| ≤ ε * H z) :
    |(∫ z, F z ∂μ) - (∫ z, G z ∂μ)| ≤
      ε * (∫ z, H z ∂μ) := by sorry
