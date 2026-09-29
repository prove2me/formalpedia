-- Prove2me | Theorems.Thm_CirclePackingConstants_thirty_six_unit_square_close_pair
-- name    : CirclePackingConstants.thirty_six_unit_square_close_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-09-22T06:56:57.141876+00:00
-- url     : https://prove2.me/theorems/147bdcc6-cfea-4ca8-99dc-9cfc2e63bded
-- title:
--   Thirty-six points in the unit square contain a close pair
-- statement:
--   For every configuration of 36 points in the unit square, two distinct points have Euclidean distance at most 1/5, equivalently squared distance at most 1/25. This is the universal point-separation obstruction needed for the upper bound r_36 ≤ 1/12.
-- source:
--   Source-faithful reduction of CirclePackingConstants.r_n_thirty_six_upper (d31aab59-e9e2-4ca3-8bd2-414bc00c1d78) to the sharp point-separation claim d_36 ≤ 1/5. The classical n=36 optimum was claimed by Kirchner and Wengerodt (1987); later surveys report gaps in that proof, so this theorem is deliberately left Open as the genuine geometric blocker rather than treated as established.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem thirty_six_unit_square_close_pair :
    ∀ p : Fin 36 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 : ℝ) / 25 := by sorry

end CirclePackingConstants
