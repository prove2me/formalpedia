-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_small_norm_retained_gap
-- name    : D1Bound5.IsD1Tuple.small_norm_retained_gap
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:02.596809+00:00
-- url     : https://prove2.me/theorems/50d7914d-af7e-40ae-8bc8-cd6f1727a756
-- title:
--   Is D1Tuple — small norm retained gap
-- statement:
--   Actual one-small-entry retained estimates in every manuscript small-norm frontier row. The alternatives state the genuine modulus cutoffs: unit first entries require B≥8 and norm-two first entries require B≥4; the remaining rows require only B≥3. Both the frontier and product-five growth inputs are proved from the tuple.
-- source:
--   D1Bound5/CoherentRetainedMixedTuple.lean, lines 70-144, SHA-256 a59ffd0af288281781f875b7951a8f6f6f4ee52341d0f2008acddd4314fcea35. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
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
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
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
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1Tuple.small_norm_retained_gap
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 5 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hN8 : ‖phi (a 0 : K)‖^2 ≤ 8)
    (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (hcase :
      (‖phi (a 0 : K)‖^2 = 1 ∧ 8 ≤ ‖phi (a 1 : K)‖) ∨
      (‖phi (a 0 : K)‖^2 = 2 ∧ 4 ≤ ‖phi (a 1 : K)‖) ∨
      ‖phi (a 0 : K)‖^2 = 3 ∨ ‖phi (a 0 : K)‖^2 = 4 ∨
      5 ≤ ‖phi (a 0 : K)‖^2)
    (H lam U : ℝ) (hrow : CoherentRetainedRow H lam U) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let R := ‖coherentVandermonde3 v‖/(‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2)
    (9999/10000 : ℝ)/lam^2 *
      (1/R-(51051/400000 : ℝ)/(‖phi (a 0 : K)‖^2*‖phi (a 1 : K)‖^2))^2 *
        (‖phi (a 0 : K)‖^2*‖phi (a 3 : K)‖^5/‖phi (a 2 : K)‖^2) < ‖phi (a 4 : K)‖ ∧
      ‖phi (a 0 : K)‖^2*‖phi (a 3 : K)‖^5/‖phi (a 2 : K)‖^2 < ‖phi (a 4 : K)‖ := by sorry

end D1Bound5
end
