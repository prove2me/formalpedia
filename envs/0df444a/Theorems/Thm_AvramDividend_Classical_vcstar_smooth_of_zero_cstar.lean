-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
-- name    : AvramDividend.Classical.vcstar_smooth_of_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:45:45.970998+00:00
-- url     : https://prove2.me/theorems/e9096d7c-0877-461c-871c-9eccb6410caf
-- title:
--   Zero-barrier candidate is twice continuously differentiable on positive reserves
-- statement:
--   If c*=0, then for all x>0 the candidate value vcstar is affine, x+v0(0). Hence vcstar is C^2 on (0,∞), with no conditions on W's differentiability. This is the zero-barrier smoothness branch of the unrestricted local verification theorem and relies solely on the previously proved affine formula.
-- source:
--   Direct consequence of the zero-barrier affine branch of Avram, Palmowski and Pistorius (2007) eq. (5.1); lemma barrierValue_zero_affine_nonnegative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_smooth_of_zero_cstar
    (W : ℝ → ℝ) (hc0 : cstar W = 0) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
  sorry
end AvramDividend.Classical
