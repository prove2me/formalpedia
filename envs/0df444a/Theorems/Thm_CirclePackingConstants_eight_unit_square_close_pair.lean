-- Prove2me | Theorems.Thm_CirclePackingConstants_eight_unit_square_close_pair
-- name    : CirclePackingConstants.eight_unit_square_close_pair
-- status  : Open
-- author  : @WillR
-- created : 2026-09-22T06:48:31.865992+00:00
-- url     : https://prove2.me/theorems/10e20652-2f2d-42dd-ab31-cd6bdeb016b5
-- title:
--   Eight points in the unit square contain a close pair
-- statement:
--   Let p_0,...,p_7 be eight points in the unit square [0,1]^2. Then there exist distinct indices i != j with squared Euclidean distance at most 2 - sqrt(3), i.e. |p_i - p_j| <= sqrt(2 - sqrt(3)). This is the point-separation form of the optimality of the eight-circle packing: d_8 = sqrt(2 - sqrt(3)) is the largest separation attainable by eight points in the unit square, so no configuration avoids a pair at distance at most d_8. Combined with the matching eight-point configuration attaining 2 - sqrt(3), it determines the optimal radius r_8 = d_8/(2(1 + d_8)). Lean formalizes points as R x R via CirclePackingConstants.Point and squared distance via CirclePackingConstants.sqDist.
-- source:
--   Erich Friedman's table of optimal packings of $n$ equal circles in a unit square (https://erich-friedman.github.io/packing/cirinsqu/), entry $n=8$; the optimal separation $d_8=sqrt(2-sqrt(3))$ and the point-separation optimality half used in Sections 4-7 of the supplied Circles in squares source package.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem eight_unit_square_close_pair : ∀ p : Fin 8 → Point, (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) → ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (2 : ℝ) - Real.sqrt 3 := by sorry

end CirclePackingConstants
