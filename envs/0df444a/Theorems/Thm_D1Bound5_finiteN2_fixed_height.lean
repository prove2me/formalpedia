-- Prove2me | Theorems.Thm_D1Bound5_finiteN2_fixed_height
-- name    : D1Bound5.finiteN2_fixed_height
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:45.188866+00:00
-- url     : https://prove2.me/theorems/25014a8a-a211-4257-b1f5-cdfc21942499
-- title:
--   Finite N2 fixed height
-- statement:
--   The kernel-checked fixed-pair coefficients give the actual strict N2 height with the printed M2, with cancellation preserved separately at every degree of the terminal parameter.
-- source:
--   D1Bound5/OneSmallN2FixedHeight.lean, lines 112-195, SHA-256 138ea5bb79e80fab3fc4acbe803d4010ac9e122dfa356c67d390a57c80b57f9c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt
















theorem _root_.D1Bound5.finiteN2_fixed_height
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (phi : K →+* ℂ) (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (e : QuadInt r.triple.tau r.triple.nu ≃+* 𝓞 K)
    (sgn conj : Bool) (x y c : 𝓞 K)
    (hx : smallExtensionSymmetry sgn conj (e.symm x) = r.triple.anchorA)
    (hy : smallExtensionSymmetry sgn conj (e.symm y) = r.triple.anchorB)
    (hy0 : phi (y : K) ≠ 0) (hC : 1000 ≤ ‖phi (c : K)‖)
    (hCB : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteN2Left (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖+
      ‖finiteN2Right (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖) <
      (r.M2 : ℝ)*‖phi (y : K)‖^4*‖phi (c : K)‖^2 := by sorry

end D1Bound5
end
