-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
-- name    : AvramDividend.Classical.avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:27:01.286879+00:00
-- url     : https://prove2.me/theorems/0dac5be6-fb93-4bc3-b757-62a28d46beca
-- title:
--   A nonpositive real marked integral equals minus its positive mark mass in toReal form
-- statement:
--   For a measurable region and any nonpositive measurable real mark, identify the Bochner integral against the restricted measure with minus the toReal of the associated nonnegative lintegral. This exact bridge is needed to turn the intrinsic signed Gaussian small-band and large-jump source integrals into adapted nonnegative original marked-jump functionals with the correct endpoints. It does not require integrability: the nonintegrable case follows the Bochner zero and ENNReal infinity-toReal conventions.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_negative_integral_eq_neg_lintegral_toReal
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hS : MeasurableSet S)
    (f : α → ℝ) (hf : Measurable f)
    (hneg : ∀ a ∈ S, f a ≤ 0) :
    (∫ a in S, f a ∂μ) =
      -((∫⁻ a in S, ENNReal.ofReal (-f a) ∂μ).toReal) := by sorry
