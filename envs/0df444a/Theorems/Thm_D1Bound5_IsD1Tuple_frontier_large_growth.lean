-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_frontier_large_growth
-- name    : D1Bound5.IsD1Tuple.frontier_large_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:51:05.25885+00:00
-- url     : https://prove2.me/theorems/9036d5f7-b64c-4864-b2f6-1f4852a3b412
-- title:
--   Is D1Tuple — frontier large growth
-- statement:
--   The sharpened FOUR-entry frontier gap: an ordered D(1)-quadruple whose smallest modulus is at least three has T>3ABS. It follows from the proved product-four constant two and a more precise entrywise use of the already-established adjugate estimates.
-- source:
--   D1Bound5/FrontierLargeTuple.lean, lines 8-81, SHA-256 912fae040f41448c6e6e89b2258d1258b75fe965d3018aff1fad40a66f5764a1. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField Matrix.Norms.L2Operator BigOperators
open Matrix Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.frontier_large_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : 3 ≤ ‖phi (a 0 : K)‖) :
    3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ <
      ‖phi (a 3 : K)‖ := by sorry

end D1Bound5
end
