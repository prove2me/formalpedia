-- Prove2me | Theorems.Thm_D1Bound5_IsD1_card_le_four_of_one_three_negative
-- name    : D1Bound5.IsD1.card_le_four_of_one_three_negative
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:58.914725+00:00
-- url     : https://prove2.me/theorems/69f6d723-39ab-4558-a225-a40bbb4b0817
-- title:
--   Is D1 — card le four of one three negative
-- statement:
--   Complete negative-entry branch of the manuscript's {1,3} lemma, over all imaginary quadratic full rings. The extra entry may be -1.
-- source:
--   D1Bound5/OneThreeNegative.lean, lines 179-239, SHA-256 608590903d9651b83081c7c7b14962c497bd29944ae7411568eb23eee5734f08. Project: https://github.com/tomislav-math/d1-bound5-lean

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




























theorem _root_.D1Bound5.IsD1.card_le_four_of_one_three_negative
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {A : Finset (𝓞 K)} (hA : IsD1 A)
    (h1 : (1 : 𝓞 K) ∈ A) (h3 : (3 : 𝓞 K) ∈ A)
    (hn : ∃ n : ℤ, n<0 ∧ (n : 𝓞 K) ∈ A) : A.card ≤ 4 := by sorry



end D1Bound5
end
