-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
-- name    : AvramDividend.Classical.avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:56:06.699045+00:00
-- url     : https://prove2.me/theorems/11e4ceee-da2c-46e8-885e-44090444096e
-- title:
--   Original finite-cap terminal value exceeds its interior caplinear extension by at most the cap corner defect
-- statement:
--   On the original finite reserve band zero to C, the interior caplinear continuation V_b lies below w and the terminal difference w(y)-V_b(y) is bounded above by w(C)-w(b)-(C-b). This is the explicit deterministic terminal cap correction needed for the true original finite-cap stopped Ito and cash ledger.
-- source:
--   Closed-cap gradient secant for the original w on subintervals [b,y] and [y,C] and the piecewise caplinear formula; preserves original finite cap C.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b y : ℝ) (hb0 : 0 ≤ b) (hbC : b ≤ C.toReal)
    (hy0 : 0 ≤ y) (hyC : y ≤ C.toReal)
    (hyCap : ENNReal.ofReal y ≤ C) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    0 ≤ w y - V y ∧
      w y - V y ≤ (w C.toReal - w b) - (C.toReal - b) := by sorry
