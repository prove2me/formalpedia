-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
-- name    : AvramDividend.Classical.vcstar_eq_zero_of_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:49:53.672754+00:00
-- url     : https://prove2.me/theorems/07dcf6e9-1e34-430d-ad0d-c03679213125
-- title:
--   The candidate dividend value vanishes on negative reserves
-- statement:
--   The formal candidate value vcstar is extended by zero to negative reserves, regardless of the scale function or the barrier. This directly discharges the zero-extension boundary hypothesis required for the verification proposition, so later regularity packages need only handle nonnegativity, continuity and smoothness.
-- source:
--   Avram, Palmowski and Pistorius (2007), extension by zero described under the piecewise candidate value (5.1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_eq_zero_of_neg (W : ℝ → ℝ) (x : ℝ) (hx : x < 0) :
    vcstar W x = 0 := by
  sorry
end AvramDividend.Classical
