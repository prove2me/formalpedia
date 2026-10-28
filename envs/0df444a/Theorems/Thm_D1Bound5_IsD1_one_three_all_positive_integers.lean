-- Prove2me | Theorems.Thm_D1Bound5_IsD1_one_three_all_positive_integers
-- name    : D1Bound5.IsD1.one_three_all_positive_integers
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:26.162986+00:00
-- url     : https://prove2.me/theorems/f963e8fe-2799-4845-bee6-6cd22c1d7548
-- title:
--   Is D1 — one three all positive integers
-- statement:
--   If a D(1)-set containing 1 and 3 has at least five entries, every entry is a positive ordinary integer, in the same full number ring.
-- source:
--   D1Bound5/OneThreeNegative.lean, lines 241-264, SHA-256 608590903d9651b83081c7c7b14962c497bd29944ae7411568eb23eee5734f08. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_IsD1

section
open scoped NumberField
open Module

namespace D1Bound5






























theorem _root_.D1Bound5.IsD1.one_three_all_positive_integers
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {A : Finset (𝓞 K)} (hA : IsD1 A)
    (h1 : (1 : 𝓞 K) ∈ A) (h3 : (3 : 𝓞 K) ∈ A) (hcard : 4<A.card) :
    ∀ z ∈ A, ∃ n : ℤ, 0<n ∧ z=(n : 𝓞 K) := by sorry

end D1Bound5
end
