-- Prove2me | Theorems.Thm_D1Bound5_halfOffDiagonal_adjugate
-- name    : D1Bound5.halfOffDiagonal_adjugate
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:06.917726+00:00
-- url     : https://prove2.me/theorems/94764e1c-c738-4db6-a89a-e847974eb0a9
-- title:
--   Half Off Diagonal adjugate
-- statement:
--   The adjugate of the reference matrix, expressed through the explicit inverse without applying Cramer's rule to individual minors.
-- source:
--   D1Bound5/ReferenceMatrixSpectral.lean, lines 62-78, SHA-256 a9d2534dbab31dc06c160d4476f3546ac57b74623f0a03cba8eaeb8e7e822001. Project: https://github.com/tomislav-math/d1-bound5-lean

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















theorem _root_.D1Bound5.halfOffDiagonal_adjugate :
    halfOffDiagonal.adjugate = (-3/16 : ℂ) • halfOffDiagonalInverse := by sorry



end D1Bound5
end
