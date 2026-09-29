-- Prove2me | Theorems.Thm_Erdos180_projectiveDirection_nonzero_right
-- name    : Erdos180.projectiveDirection_nonzero_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:15:27.200357+00:00
-- url     : https://prove2.me/theorems/a9cd746a-9e71-46e5-bafe-706096976a72
-- title:
--   A nonzero determinant forces a nonzero second direction
-- statement:
--   If $xy' - x'y \ne 0$ then $(x',y') \ne (0,0)$. The companion of the preceding lemma.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L6621-L6629

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Push

open Erdos180
variable (K : Type*) [Field K]

theorem Erdos180.projectiveDirection_nonzero_right
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x' ≠ 0 ∨ y' ≠ 0 := by sorry
