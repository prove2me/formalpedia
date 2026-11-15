-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
-- name    : AvramDividend.Classical.avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:18:15.561924+00:00
-- url     : https://prove2.me/theorems/2dfc06da-7ff6-4704-ba5c-1d61e6ef46b1
-- title:
--   Ordinary integral of a real square equals the finite extended squared-norm integral
-- statement:
--   An integrable square has its real integral equal to the real conversion of the extended nonnegative integral of the squared nonnegative norm.
-- source:
--   Mathlib integral_eq_lintegral_of_nonneg_ae and pointwise Real.norm square identity.

import Mathlib
open MeasureTheory ENNReal Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : Integrable (fun ω => (f ω)^2) μ) :
    (∫ ω, (f ω)^2 ∂μ) =
      (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞)^2 ∂μ).toReal := by sorry
