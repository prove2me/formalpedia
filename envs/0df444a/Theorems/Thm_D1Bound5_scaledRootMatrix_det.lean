-- Prove2me | Theorems.Thm_D1Bound5_scaledRootMatrix_det
-- name    : D1Bound5.scaledRootMatrix_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:37.543532+00:00
-- url     : https://prove2.me/theorems/99dbca54-c718-4500-bd86-0c7ca4ad5c7f
-- title:
--   Scaled Root Matrix det
-- statement:
--   Exact determinant scaling in arbitrary finite dimension, with no nonzero-root assumption.
-- source:
--   D1Bound5/DeterminantNormalization.lean, lines 23-32, SHA-256 196cc874899f4fdc78056f81619aaf82ead08fc052cbd1257526b60749c0f0be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions

section
open scoped BigOperators
open Matrix

namespace D1Bound5






theorem _root_.D1Bound5.scaledRootMatrix_det {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (u : n → R) (M : Matrix n n R) :
    (scaledRootMatrix u M).det = (∏ i, u i)^2 * M.det := by sorry













end D1Bound5
end
