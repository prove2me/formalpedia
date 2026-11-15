-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
-- name    : AvramDividend.Classical.avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:06:44.038726+00:00
-- url     : https://prove2.me/theorems/9aec2675-52a0-4d75-8334-f2dc6ae3cdf1
-- title:
--   Original finite-cap physical clipping sequence has a nonpositive Gaussian local-time slope jump
-- statement:
--   At every interior rational clipping cap b_j=C*(j+1)/(j+2) of the original finite-cap Gaussian verification argument, the glued cap-linear payoff has left derivative w′(b_j), right derivative one, and a nonpositive jump of slope. This directly certifies the favourable sign of the Itô-Tanaka local-time term on the true clipping sequence.
-- source:
--   Original finite-cap strict-interior rational clipping bound B41 and Proved Gaussian interior one-sided derivative/kink certificate avram_gbB42_original_finitecap_interior_kink_favourable_localtime.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_finitecap_interior_kink_favourable_localtime
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b ∧
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b ∧
    1 - deriv w b ≤ 0 := by sorry
