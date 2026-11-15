-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
-- name    : AvramDividend.Classical.avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:33:43.439444+00:00
-- url     : https://prove2.me/theorems/973cf9b8-6a19-44d0-9257-002eb680709a
-- title:
--   Original finite-cap interior clipping corner-defect and upper band are nonnegative
-- statement:
--   For each original finite-cap interior clipping level b_j=C*(j+1)/(j+2), the level lies between zero and C, and the value-function corner defect w(C)-w(b_j)-(C-b_j) is nonnegative from the derivative lower bound. This supplies the exact nonnegative corner allowance of the original Gaussian stopped cash budget.
-- source:
--   Existing gfinite61 source derives exactly this geometric secant consequence; it is isolated as an independently proved import for B21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
open Set MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB37_original_finitecap_interior_clip_gap_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 ≤ b ∧ b ≤ C.toReal ∧
      0 ≤ (w C.toReal - w b) - (C.toReal - b) := by sorry
