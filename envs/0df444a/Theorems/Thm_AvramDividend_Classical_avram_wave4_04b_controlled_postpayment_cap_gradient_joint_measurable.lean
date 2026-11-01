-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_cap_gradient_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_cap_gradient_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:12:24.068981+00:00
-- url     : https://prove2.me/theorems/3923731c-6b4a-4e72-8fc9-9e9eb2cf6a82
-- title:
--   Actual controlled postpayment capped interior derivative jointly measurable in time and probability
-- statement:
--   For the actual source Lévy X, the same adapted right-dividend strategy D, and w twice continuously differentiable only on the strict ENNReal-capped interior, the derivative evaluated at the true postpayment controlled reserve and extended by zero off the interior is jointly Borel measurable in time and sample point. This supplies the sample-dependent finite-variation correction integrand without global C² assumptions or artificial independent copies.
-- source:
--   Compose Proved postPaymentReserve_cadlag_adapted and rightContinuous_measurable_sections_joint_evaluation with Proved exact cap derivative-zero-extension

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_cap_interior_deriv_zero_extension

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_cap_gradient_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < x + X.X z.1 z.2 - rightLimit D z.1 z.2 ∧
        ENNReal.ofReal (x + X.X z.1 z.2 - rightLimit D z.1 z.2) < C
      then deriv w (x + X.X z.1 z.2 - rightLimit D z.1 z.2)
      else 0) := by
  sorry
