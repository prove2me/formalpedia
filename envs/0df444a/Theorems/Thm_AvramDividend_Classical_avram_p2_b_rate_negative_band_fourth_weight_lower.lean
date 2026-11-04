-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_fourth_weight_lower
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_band_fourth_weight_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:14:36.570293+00:00
-- url     : https://prove2.me/theorems/d984573b-a8e2-4126-891b-7a21f06576de
-- title:
--   The fourth exponential jump weight is bounded below on a separated negative band
-- statement:
--   For positive theta and epsilon, and every negative jump mark y at most negative epsilon, the fourth power (exp(theta*y)-1)^4 is at least the strictly positive deterministic constant (1-exp(-theta*epsilon))^4. This exact deterministic inequality is required for safe division of the fourth-weighted small-time jump measure on a negative band away from zero, and follows from monotonicity of the exponential and nonnegative fourth power.

import Mathlib
open Real

theorem AvramDividend.Classical.avram_p2_b_rate_negative_band_fourth_weight_lower
    (θ ε y : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (hy : y ≤ -ε) :
    (1 - Real.exp (-θ * ε)) ^ 4 ≤
      (Real.exp (θ * y) - 1) ^ 4 := by sorry
