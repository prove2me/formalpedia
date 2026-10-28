-- Prove2me | Theorems.Thm_D1Bound5_productFour_growth_from_bounds
-- name    : D1Bound5.productFour_growth_from_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:42.8159+00:00
-- url     : https://prove2.me/theorems/5411d2cf-4a32-4e11-b6d5-05123bf0dfdc
-- title:
--   Product Four growth from bounds
-- statement:
--   The final numerical implication D > 2ABC, conditional on the integral determinant lower bound and the perturbative estimates.
-- source:
--   D1Bound5/ProductFourNumericalClosure.lean, lines 55-74, SHA-256 fb992c197fe0f50a9f89f189349d42efc0b35d9ebec71e17006e6846eae15712. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.productFour_growth_from_bounds
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (A B C D : ℝ) (hD : 18 < D)
    (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourH * productFourS^3)
    (hadj : ‖F.adjugate‖ < productFourH * productFourS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2)
    (hlower : A*B*C*D ≤ ‖(F + Matrix.vecMulVec w w).det‖) :
    2*A*B*C < D := by sorry

end D1Bound5
end
