-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_height_envelope
-- name    : D1Bound5.IsD1Tuple.ordinary_height_envelope
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:10:11.57977+00:00
-- url     : https://prove2.me/theorems/744bf5c4-f176-460e-82c8-7ee1e0ccbab6
-- title:
--   Is D1Tuple — ordinary height envelope
-- statement:
--   The manuscript ordinary height envelope for an actual ordered D(1)-quadruple. The all-order analytic estimate is obtained internally from the constructed integral Bennett matrix and the tuple's roots.
-- source:
--   D1Bound5/FullRingOrdinaryHeight.lean, lines 30-90, SHA-256 8899269e1cc08e9d24a38236bc862c59ba7f8badc869787d9bb0f0e08c91243a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.ordinary_height_envelope
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hAC : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (a 2 : K)‖)
    (hC : 4*‖phi (a 1 : K)‖ < ‖phi (a 2 : K)‖)
    (h r u : ℝ)
    (hHlog : ordinaryLog10 (42*‖phi (a 1 : K)‖^3*‖phi (a 2 : K)‖) <
      ordinaryLog10 ‖phi (a 2 : K)‖+h)
    (hRlog : 2*ordinaryLog10 ‖phi (a 2 : K)‖+r <
      ordinaryLog10 (bennettTwoResidualRate ‖phi (a 0 : K)‖ ‖phi (a 1 : K)‖
        ‖phi (a 2 : K)‖ ‖phi (a 0 : K)-phi (a 1 : K)‖))
    (hUlog : ordinaryLog10 (253*‖phi (a 1 : K)‖^2) < u)
    (hxt : h-r < ordinaryLog10 ‖phi (a 2 : K)‖)
    (hx2 : 0 < 2*ordinaryLog10 ‖phi (a 2 : K)‖+r) :
    ordinaryLog10 ‖phi (a 3 : K)‖ < 7*ordinaryLog10 ‖phi (a 2 : K)‖+
      (4*u+8*h-4*r)+(2*u*r+(4*u+8*h-4*r)*(h-r))/
        (ordinaryLog10 ‖phi (a 2 : K)‖-(h-r))+(2/5 : ℝ) := by sorry

end D1Bound5
end
