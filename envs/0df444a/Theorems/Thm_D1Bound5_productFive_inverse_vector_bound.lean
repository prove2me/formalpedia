-- Prove2me | Theorems.Thm_D1Bound5_productFive_inverse_vector_bound
-- name    : D1Bound5.productFive_inverse_vector_bound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:55.644679+00:00
-- url     : https://prove2.me/theorems/1b09be76-cd0a-4c5c-8505-009bf97b90b8
-- title:
--   Product Five inverse vector bound
-- statement:
--   An L2 inverse-vector bound that exploits the constant reference eigenvector. The coordinatewise last-column estimate is deliberately an explicit input.
-- source:
--   D1Bound5/ProductFiveInverseVector.lean, lines 29-130, SHA-256 425de7cb6ba343c242be88e9088726741289138c3dff82b0611bd3b9f173bbee. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5










theorem _root_.D1Bound5.productFive_inverse_vector_bound
    (F : Matrix (Fin 4) (Fin 4) ℂ) (v : Fin 4 → ℂ)
    (hnear : ‖F - halfOffDiagonal‖ ≤ (11/96 : ℝ))
    (hv : ‖(WithLp.toLp 2 (fun i => v i - (1/2 : ℂ)) :
        EuclideanSpace ℂ (Fin 4))‖ < (1/200 : ℝ)) :
    ‖(WithLp.toLp 2 (F⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin 4))‖ <
      (11/12 : ℝ) := by sorry

end D1Bound5
end
