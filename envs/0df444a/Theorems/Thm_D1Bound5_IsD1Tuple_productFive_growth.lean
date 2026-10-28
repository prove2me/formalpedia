-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_productFive_growth
-- name    : D1Bound5.IsD1Tuple.productFive_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:18.68889+00:00
-- url     : https://prove2.me/theorems/831e6cd7-4aa6-445d-b29a-1b943c8d4283
-- title:
--   Is D1Tuple — product Five growth
-- statement:
--   The product-five growth lemma for an actual ordered D(1) quintuple in the full ring of integers of every imaginary quadratic field.
-- source:
--   D1Bound5/ProductFiveTupleGrowth.lean, lines 97-122, SHA-256 80d98052c4994147171c28574e3e10fcf54fe865d2b39c5d757ddcc0ffb46c5d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1Tuple

section
open scoped NumberField Matrix.Norms.L2Operator
open Matrix Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.productFive_growth
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : 3 ≤ ‖phi (a 1 : K)‖) :
    3 * (∏ i : Fin 4, ‖phi (a (Fin.castAdd 1 i) : K)‖) <
      ‖phi (a 4 : K)‖ := by sorry

end D1Bound5
end
