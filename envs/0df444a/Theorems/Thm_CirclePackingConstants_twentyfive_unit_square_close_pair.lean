-- Prove2me | Theorems.Thm_CirclePackingConstants_twentyfive_unit_square_close_pair
-- name    : CirclePackingConstants.twentyfive_unit_square_close_pair
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-23T14:13:01.21081+00:00
-- url     : https://prove2.me/theorems/d684404f-77b8-4e70-9531-f0384eff2e8d
-- title:
--   Twenty-five points in the unit square have a close pair
-- statement:
--   Any twenty-five points in the unit square contain two distinct points at squared distance at most $1/16$.
--
--   This is the pigeonhole core of the five-by-five grid upper bound: with $r_{25}=1/10$ the separation scale is $d=1/4$. Like its sixteen-point sibling it separates finite combinatorics from the routine packing normalization.
--
--   **Formalization Note** The bound is stated evaluated ($1/16$ rather than $(1/4)^2`).
-- source:
--   Circle packing in a square, five-by-five grid upper bound (Section 7): plotted against the proved three-by-three analogue. Companion to the six- and eight-point close-pair lemmas.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem twentyfive_unit_square_close_pair : forall p : Fin 25 -> Point, (forall i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) -> exists i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 : Rat)/16 := by sorry

end CirclePackingConstants
