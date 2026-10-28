-- Prove2me | Theorems.Thm_D1Bound5_productFour_rankOne_numeric
-- name    : D1Bound5.productFour_rankOne_numeric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:46:29.004429+00:00
-- url     : https://prove2.me/theorems/2c47490d-d5c6-43bd-bcb9-f9bc6830749d
-- title:
--   Product Four rank One numeric
-- statement:
--   The rank-one determinant bound reduces the large-entry branch to the two still-open perturbative determinant and adjugate estimates. These estimates are assumptions here, not asserted as established.
-- source:
--   D1Bound5/ProductFourNumericalClosure.lean, lines 22-53, SHA-256 fb992c197fe0f50a9f89f189349d42efc0b35d9ebec71e17006e6846eae15712. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ProductFourNumericalClosure_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5








theorem _root_.D1Bound5.productFour_rankOne_numeric
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (D : ℝ) (hD : 18 < D)
    (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourH * productFourS^3)
    (hadj : ‖F.adjugate‖ < productFourH * productFourS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2) :
    ‖(F + Matrix.vecMulVec w w).det‖ < D^2 / 2 := by sorry



end D1Bound5
end
