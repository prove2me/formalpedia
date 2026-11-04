-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower
-- name    : AvramDividend.Classical.avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:58:00.427622+00:00
-- url     : https://prove2.me/theorems/8c484bea-1df0-48b3-b7ee-1aa10f1d2e7b
-- title:
--   Fourth-exponential Lévy test admits uniform separated negative-band lower bound
-- statement:
--   For any positive test exponent theta and separation epsilon, the fourth-power exponential mark weight at a real y at most negative epsilon is bounded below by its positive boundary value at negative epsilon. This deterministic analytic inequality allows weighted Levy tests to control finite negative-band measure without assuming the original jump rate.

import Mathlib

open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower (θ ε y : ℝ) (hθ : 0 < θ) (hε : 0 < ε)
    (hy : y ≤ -ε) :
    (1 - Real.exp (-θ * ε)) ^ 4 ≤ (Real.exp (θ * y) - 1) ^ 4 := by sorry
