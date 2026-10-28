-- Prove2me | Theorems.Thm_D1Bound5_productFive_quadratic_q_div_norm_lt
-- name    : D1Bound5.productFive_quadratic_q_div_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:17:23.378127+00:00
-- url     : https://prove2.me/theorems/813324f4-c4bb-455f-af5a-2964d5ee1b16
-- title:
--   Product Five quadratic q div norm lt
-- statement:
--   The quadratic bilinear form involving the first-four-entry vector is small relative to the square of the last entry. Neither the matrix nor its inverse is assumed Hermitian.
-- source:
--   D1Bound5/ProductFiveNormalizedQuadratic.lean, lines 9-48, SHA-256 f9e9847eb9518578e87809242291d3fb011ca50556f7c98e56d8bd121a0e2e9d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5


theorem _root_.D1Bound5.productFive_quadratic_q_div_norm_lt
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ) (d : ℂ)
    (hd : d ≠ 0)
    (hnear : ‖F - halfOffDiagonal‖ < (1/8 : ℝ))
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin 4))‖ < ‖d‖ / 9) :
    ‖(w ⬝ᵥ (F⁻¹ *ᵥ w))/d^2‖ < (8/243 : ℝ) := by sorry



end D1Bound5
end
