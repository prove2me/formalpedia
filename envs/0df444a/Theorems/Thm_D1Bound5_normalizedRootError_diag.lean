-- Prove2me | Theorems.Thm_D1Bound5_normalizedRootError_diag
-- name    : D1Bound5.normalizedRootError_diag
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:27:51.54251+00:00
-- url     : https://prove2.me/theorems/34061fa3-0789-4e6a-8a2d-c79d038a9035
-- title:
--   Normalized Root Error diag
-- statement:
--   The correction is zero on the diagonal.
-- source:
--   D1Bound5/DeterminantNormalization.lean, lines 57-67, SHA-256 196cc874899f4fdc78056f81619aaf82ead08fc052cbd1257526b60749c0f0be. Project: https://github.com/tomislav-math/d1-bound5-lean

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












theorem _root_.D1Bound5.normalizedRootError_diag {R n : Type*} [CommRing R]
    (a u : n → R) (M : Matrix n n R)
    (hu : ∀ i, (u i)^2 = a i) (hd : ∀ i, M i i = a i)
    (i : n) : normalizedRootError a u M i i = 0 := by sorry







end D1Bound5
end
