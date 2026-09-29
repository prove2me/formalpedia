-- Prove2me | Theorems.Thm_CirclePackingConstants_seven_unit_square_close_pair
-- name    : CirclePackingConstants.seven_unit_square_close_pair
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T17:30:00.090687+00:00
-- url     : https://prove2.me/theorems/d0d13d4e-155e-442e-9dda-931783f5bd8f
-- title:
--   Seven points in the unit square contain a close pair
-- statement:
--   Let $p_0,\ldots,p_6$ be seven points in the unit square $[0,1]^2$. Then two of the points are at squared Euclidean distance at most $(4-2\sqrt3)^2$; equivalently, some pair is at distance at most $4-2\sqrt3$.
--
--   $$\exists i\ne j,\qquad |p_i-p_j|^2\le (4-2\sqrt3)^2.$$
--
--   This is the global optimality statement for the normalized seven-point problem. Together with the affine normalization from disk centers to points in the unit square, it yields the upper bound on the supremal radius for seven equal disks.
-- source:
--   User-supplied circles_in_square_n7.pdf, p. 7 (Global optimality theorem: among seven points in the unit square some pair has distance at most 4 - 2*sqrt 3), with the exact integer verifier in Appendix A, pp. 10-12.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem seven_unit_square_close_pair :
    ∀ p : Fin 7 → Point,
      (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
      ∃ i j, i ≠ j ∧
        sqDist (p i) (p j) ≤ (4 - 2 * Real.sqrt 3) ^ 2 := by sorry
