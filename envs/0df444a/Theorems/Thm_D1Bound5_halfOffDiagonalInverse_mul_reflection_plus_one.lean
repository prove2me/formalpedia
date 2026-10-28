-- Prove2me | Theorems.Thm_D1Bound5_halfOffDiagonalInverse_mul_reflection_plus_one
-- name    : D1Bound5.halfOffDiagonalInverse_mul_reflection_plus_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:03.287224+00:00
-- url     : https://prove2.me/theorems/1f25cef2-05a7-4855-a563-0736fdf29ee0
-- title:
--   Half Off Diagonal Inverse mul reflection plus one
-- statement:
--   Auxiliary result `halfOffDiagonalInverse_mul_reflection_plus_one` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/ReferenceInverseNorm.lean, lines 55-62, SHA-256 53050c6b49ff7b7eabf281a545ecf66dea734cd088fd701c36f0829189368aeb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ReferenceInverseNorm_Definitions
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5













theorem _root_.D1Bound5.halfOffDiagonalInverse_mul_reflection_plus_one :
    halfOffDiagonalInverse *
      ((1 : Matrix (Fin 4) (Fin 4) ℂ) + referenceReflection) =
      (-2 : ℂ) • ((1 : Matrix (Fin 4) (Fin 4) ℂ) + referenceReflection) := by sorry







end D1Bound5
end
