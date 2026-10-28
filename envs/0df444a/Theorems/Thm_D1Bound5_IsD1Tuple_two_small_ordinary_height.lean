-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_two_small_ordinary_height
-- name    : D1Bound5.IsD1Tuple.two_small_ordinary_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:59:12.325853+00:00
-- url     : https://prove2.me/theorems/66cc0c1d-7717-4df9-892d-0d2a65a82ff1
-- title:
--   Is D1Tuple — two small ordinary height
-- statement:
--   The uniform ordinary height bound for two small anchors, derived from the actual integral Bennett rows of the given quadruple.
-- source:
--   D1Bound5/TwoSmallOrdinaryHeight.lean, lines 10-90, SHA-256 e2552609c32a48ca7942880be1c71c76b5c34fb2582e228c1345936b5eda4e5a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.IsD1Tuple.two_small_ordinary_height
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : ‖phi (a 1 : K)‖ < 3)
    (hP : (10 : ℝ)^8 ≤ ‖phi (a 2 : K)‖) :
    ordinaryLog10 ‖phi (a 3 : K)‖ <
      twoSmallHeightEnvelope (ordinaryLog10 ‖phi (a 2 : K)‖) := by sorry

end D1Bound5
end
