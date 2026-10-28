-- Prove2me | Theorems.Thm_D1Bound5_full_ring_all_large_retained_monomial
-- name    : D1Bound5.full_ring_all_large_retained_monomial
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:21.596091+00:00
-- url     : https://prove2.me/theorems/ab710635-58ce-4f96-8343-e75c029e2a53
-- title:
--   Full ring all large retained monomial
-- statement:
--   With the sharpened four-entry frontier, the retained actual tuple gap gives the coefficient 400 used in the no-small-entry overlap table.
-- source:
--   D1Bound5/CoherentRetainedGap.lean, lines 83-134, SHA-256 5374758cbafe23ef4c1439e82acf3ae6083ddbae04f6692091ae5c447ee08b87. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.full_ring_all_large_retained_monomial
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖) :
    400*(‖phi (a 0 : K)‖^7*‖phi (a 1 : K)‖^5*‖phi (a 2 : K)‖^3) < ‖phi (a 4 : K)‖ := by sorry

end D1Bound5
end
