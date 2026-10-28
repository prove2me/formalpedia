-- Prove2me | Theorems.Thm_D1Bound5_inverse_mul_halfOffDiagonal
-- name    : D1Bound5.inverse_mul_halfOffDiagonal
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:24:51.437009+00:00
-- url     : https://prove2.me/theorems/e6bc71a0-1fea-42dc-bc6a-7d5407790479
-- title:
--   Inverse mul half Off Diagonal
-- statement:
--   The other inverse identity is also an equality over complex matrices.
-- source:
--   D1Bound5/ReferenceMatrixSpectral.lean, lines 23-29, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5






theorem _root_.D1Bound5.inverse_mul_halfOffDiagonal :
    halfOffDiagonalInverse * halfOffDiagonal = 1 := by sorry












end D1Bound5
end
