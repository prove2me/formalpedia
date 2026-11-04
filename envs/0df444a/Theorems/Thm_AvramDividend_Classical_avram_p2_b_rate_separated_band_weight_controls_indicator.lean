-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_separated_band_weight_controls_indicator
-- name    : AvramDividend.Classical.avram_p2_b_rate_separated_band_weight_controls_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:22:02.719316+00:00
-- url     : https://prove2.me/theorems/64dfe0ca-9b97-40c1-84e3-f4fd5dbb713c
-- title:
--   Uniform fourth-exponential domination of a separated negative-jump indicator
-- statement:
--   For any positive fourth-exponential rate and positive negative-band separation, the fourth power weight (exp(theta*y)-1)^4 uniformly dominates the indicator of y <= -epsilon by a strictly positive band-independent constant. This establishes the pointwise domination needed for original-process O(h) negative-increment estimates and subsequent weighted-measure inversion.

import Mathlib

theorem AvramDividend.Classical.avram_p2_b_rate_separated_band_weight_controls_indicator
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    0 < (1 - Real.exp (-θ * ε)) ^ 4 ∧
      ∀ y : ℝ,
        (1 - Real.exp (-θ * ε)) ^ 4 *
          (if y ≤ -ε then (1 : ℝ) else 0) ≤
        (Real.exp (θ * y) - 1) ^ 4 := by sorry
