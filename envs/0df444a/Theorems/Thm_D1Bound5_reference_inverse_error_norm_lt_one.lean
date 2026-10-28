-- Prove2me | Theorems.Thm_D1Bound5_reference_inverse_error_norm_lt_one
-- name    : D1Bound5.reference_inverse_error_norm_lt_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:13:51.902489+00:00
-- url     : https://prove2.me/theorems/925f7f3e-0063-4298-8692-8a52840650d8
-- title:
--   Reference inverse error norm lt one
-- statement:
--   The sharp reference inverse norm makes the normalized correction a strict contraction when all pair products have modulus at least nine.
-- source:
--   D1Bound5/ReferenceInverseNorm.lean, lines 88-101, SHA-256 53050c6b49ff7b7eabf281a545ecf66dea734cd088fd701c36f0829189368aeb. Project: https://github.com/tomislav-math/d1-bound5-lean

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




















theorem _root_.D1Bound5.reference_inverse_error_norm_lt_one
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (hnear : ‖F - halfOffDiagonal‖ < 3 * (128/8649 : ℝ)) :
    ‖halfOffDiagonalInverse * (F - halfOffDiagonal)‖ < 1 := by sorry

end D1Bound5
end
