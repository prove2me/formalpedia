-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:35:34.317476+00:00
-- url     : https://prove2.me/theorems/36cfdb7a-038d-423d-8d71-1669e1efef32
-- title:
--   Original physical finite clock signed Fubini L1 expected cash bridge
-- statement:
--   At the actual original bounded mapped-Lebesgue physical time clock times the original path probability P, an explicit product-space L1 residual with nonpositive product integral has a genuinely integrable pathwise time integral with nonpositive expectation. The accepted original clock mass theorem supplies a finite measure instance and Mathlib Fubini justifies the expectation/time-integral swap. This is a conditional analytic bridge, with no independent source compensator or hidden optional stopping.
-- source:
--   Proved avram_p3_b_bvjump_original_physical_clock_total_mass_finite plus Mathlib integral_prod_symm and Integrable.integral_prod_right

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_physical_clock_total_mass_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_true_clock_integrable_signed_Fubini_mean_bound{Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T : ℝ≥0) (F : ℝ≥0 × Ω → ℝ)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P))
    (hFmean : (∫ p, F p ∂((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) ≤ 0) :
    Integrable (fun ω => (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal))) P ∧
    (∫ ω, (∫ t, F (t, ω)
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal)) ∂P) ≤ 0 := by sorry
