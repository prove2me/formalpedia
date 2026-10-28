-- Prove2me | Theorems.Thm_D1Bound5_productFour_mixed_rankOne_numeric
-- name    : D1Bound5.productFour_mixed_rankOne_numeric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:21.648238+00:00
-- url     : https://prove2.me/theorems/92ff3a3d-6a68-4796-9bba-b751a611b313
-- title:
--   Product Four mixed rank One numeric
-- statement:
--   The mixed rank-one determinant inequality.
-- source:
--   D1Bound5/MixedProductFourGrowth.lean, lines 55-84, SHA-256 6405700c83d4efaa313716abc06975c43c8dd7320d44c6d848be130386d5f504. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_MixedProductFourGrowth_Definitions

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5









theorem _root_.D1Bound5.productFour_mixed_rankOne_numeric
    (F : Matrix (Fin 4) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (D : ℝ) (hD : 18 < D) (hF : F.det ≠ 0)
    (hdet : ‖F.det‖ < productFourMixedH * productFourMixedS^3)
    (hadj : ‖F.adjugate‖ < productFourMixedH * productFourMixedS^2)
    (hw : (∑ i, ‖w i‖^2) ≤ (13/12 : ℝ) * D^2) :
    ‖(F + Matrix.vecMulVec w w).det‖ < (2/3 : ℝ)*D^2 := by sorry








end D1Bound5
end
