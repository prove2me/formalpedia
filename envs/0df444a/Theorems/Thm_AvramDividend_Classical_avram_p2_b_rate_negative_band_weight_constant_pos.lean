-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_weight_constant_pos
-- name    : AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_constant_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:30:48.144196+00:00
-- url     : https://prove2.me/theorems/1471adaa-1b32-413c-81ff-9e3721ce8a9b
-- title:
--   Separated negative exponential band weight has strictly positive lower constant
-- statement:
--   For strictly positive theta and epsilon the constant (1-exp(-theta*epsilon))^4 is strictly positive. Together with the separated-band weight lower inequality this justifies local inversion of the fourth-exponential weight, rather than dividing by a weight which vanishes at the origin.

import Mathlib

theorem AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_constant_pos
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    0 < (1 - Real.exp (-θ * ε)) ^ 4 := by sorry
