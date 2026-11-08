-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen13_affine_kernel_density_interval_integral
-- name    : AvramDividend.Classical.avram_gen13_affine_kernel_density_interval_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:17:33.835358+00:00
-- url     : https://prove2.me/theorems/ad7474d1-a6c6-4973-9795-09e605354aa5
-- title:
--   Exact negative-jump affine kernel integral in the singular positive-density coordinates
-- statement:
--   For a positive reserve no larger than one, integrate the exact affine ruin-crossing jump kernel against the proposed singular jump density after changing the negative jump mark to its magnitude. The result is expressed using the already proved half-power and three-halves-power tails.
-- source:
--   Exact analytic integration child for the source generator; this theorem does not yet identify the original Levy measure or random stopped reserve.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gen13_affine_kernel_density_interval_integral
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ r in y..1, (r ^ (-(1 / 2 : ℝ)) -
      (1 + y) * r ^ (-(3 / 2 : ℝ)))) =
      2 * (1 - y ^ (1 / 2 : ℝ)) -
      (1 + y) * (2 * (y ^ (-(1 / 2 : ℝ)) - 1)) := by sorry
