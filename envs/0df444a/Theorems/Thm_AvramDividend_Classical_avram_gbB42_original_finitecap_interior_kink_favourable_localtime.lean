-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_finitecap_interior_kink_favourable_localtime
-- name    : AvramDividend.Classical.avram_gbB42_original_finitecap_interior_kink_favourable_localtime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:48:34.35292+00:00
-- url     : https://prove2.me/theorems/69ee8585-324e-4f1e-938a-fea4b8b8348e
-- title:
--   Original finite-cap interior clipping kink has nonpositive local-time coefficient without cap C2
-- statement:
--   Given the original C2 smoothness and gradient bound only strictly inside the finite cap C, an interior clipping b has left derivative w-prime(b), right derivative one and kink jump 1-w-prime(b) ≤0. Hence the Tanaka or Ito–Meyer local-time correction has the favourable nonpositive sign, with no differentiability required at C.
-- source:
--   Proved gfinite53 interior derivative certificate and wave5_05 one-sided caplinear kink identity at strictly interior b.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite53_original_interior_C2_derivative_certificates
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB42_original_finitecap_interior_kink_favourable_localtime
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb0 : 0 < b) (hbC : ENNReal.ofReal b < C) :
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b ∧
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b ∧
    1 - deriv w b ≤ 0 := by sorry
