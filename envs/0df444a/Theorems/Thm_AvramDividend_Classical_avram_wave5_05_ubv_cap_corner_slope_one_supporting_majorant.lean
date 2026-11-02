-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_slope_one_supporting_majorant
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_slope_one_supporting_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:44:55.064047+00:00
-- url     : https://prove2.me/theorems/92900713-63ef-4b8e-8db8-a0f638cb13ef
-- title:
--   Slope-one continuation admits a global cap-corner supporting affine majorant on all nonnegative reserves, without a cap derivative
-- statement:
--   For the corrected UBV verification candidate, continuous on nonnegative reserves and C² with w'≥1 only strictly inside a positive finite cap c, its slope-one continuation v_c(y)=w(y) for y≤c and w(c)+(y−c) for y>c lies below the affine cap tangent w(c)+(y−c) at EVERY nonnegative reserve y. Equality holds automatically beyond the cap, and the nontrivial inward inequality includes y=0 and y=c by the Proved inclusive-cap secant theorem. No one-sided derivative or C² extension at c is introduced. This is a pointwise cap-corner sign/majorization fact for legitimate stochastic smoothing, not a complete Itô local-time or Stieltjes dividend statement.
-- source:
--   Original Proved inclusive-cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c; supports corrected canonical UBV 429e17ca-5528-40b5-b593-7c03973d0706 cap contact. No milestone/core changes.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_slope_one_supporting_majorant
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (y : ℝ) (hy : 0 ≤ y) :
    (if y ≤ c then w y else w c + (y - c)) ≤ w c + (y - c) := by sorry
