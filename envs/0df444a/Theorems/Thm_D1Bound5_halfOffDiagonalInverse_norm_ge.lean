-- Prove2me | Theorems.Thm_D1Bound5_halfOffDiagonalInverse_norm_ge
-- name    : D1Bound5.halfOffDiagonalInverse_norm_ge
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:42.152799+00:00
-- url     : https://prove2.me/theorems/303cdd61-24bc-4b07-b7e9-1e13d75b7e36
-- title:
--   Half Off Diagonal Inverse norm ge
-- statement:
--   Auxiliary result `halfOffDiagonalInverse_norm_ge` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/ReferenceInverseNorm.lean, lines 64-82, SHA-256 53050c6b49ff7b7eabf281a545ecf66dea734cd088fd701c36f0829189368aeb. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5















theorem _root_.D1Bound5.halfOffDiagonalInverse_norm_ge :
    2 ≤ ‖halfOffDiagonalInverse‖ := by sorry





end D1Bound5
end
