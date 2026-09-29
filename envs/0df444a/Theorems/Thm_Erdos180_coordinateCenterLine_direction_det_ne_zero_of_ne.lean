-- Prove2me | Theorems.Thm_Erdos180_coordinateCenterLine_direction_det_ne_zero_of_ne
-- name    : Erdos180.coordinateCenterLine_direction_det_ne_zero_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:17:59.069309+00:00
-- url     : https://prove2.me/theorems/0b9a80dd-b421-42c9-a76c-8742443197e8
-- title:
--   Distinct coordinate centres have independent directions
-- statement:
--   If two coordinate centre lines are distinct then their directions satisfy
--   $xy' - x'y \ne 0$.
--
--   Two distinct common centres therefore give two independent directions, and by the previous
--   classification a third base having both of them as common centres must be orthogonal to a whole
--   projective line's worth of points — the contradiction that rules out a $J$-pattern in
--   Proposition 4.2.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7798-L7866

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.coordinateCenterLine_direction_det_ne_zero_of_ne
    {x y x' y' : K}
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hxy' : x' ≠ 0 ∨ y' ≠ 0)
    (hne : coordinateCenterLine K x y hxy ≠
      coordinateCenterLine K x' y' hxy') :
    x * y' - x' * y ≠ 0 := by sorry
