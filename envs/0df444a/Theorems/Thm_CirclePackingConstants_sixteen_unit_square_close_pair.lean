-- Prove2me | Theorems.Thm_CirclePackingConstants_sixteen_unit_square_close_pair
-- name    : CirclePackingConstants.sixteen_unit_square_close_pair
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-23T14:13:07.313694+00:00
-- url     : https://prove2.me/theorems/b47e19b8-dcc5-41b7-893f-401caa1484be
-- title:
--   Sixteen points in the unit square have a close pair
-- statement:
--   Any sixteen points in the unit square contain two distinct points at squared distance at most $1/9$.
--
--   This is the pigeonhole core of the four-by-four grid upper bound: with $r_{16}=1/8$ the separation scale is $d=1/3$, and this lemma supplies exactly the close pair at that scale. It separates the finite combinatorics from the packing normalization (inner square, scaling, ssup argument), which is routine once this is available.
--
--   **Formalization Note** The bound is stated evaluated ($1/9$ rather than $(1/3)^2$); the reduction rewrites it via `norm_num`.
-- source:
--   Circle packing in a square, four-by-four grid upper bound (Section 7): plotted against the proved three-by-three analogue. Companion to the six- and eight-point close-pair lemmas.

import Definitions.Def_CirclePackingConstants

namespace CirclePackingConstants

theorem sixteen_unit_square_close_pair : forall p : Fin 16 -> Point, (forall i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) -> exists i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (1 : Rat)/9 := by sorry

end CirclePackingConstants
