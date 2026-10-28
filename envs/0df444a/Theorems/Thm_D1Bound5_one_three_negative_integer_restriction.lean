-- Prove2me | Theorems.Thm_D1Bound5_one_three_negative_integer_restriction
-- name    : D1Bound5.one_three_negative_integer_restriction
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:40:18.543003+00:00
-- url     : https://prove2.me/theorems/b00fba0f-ff73-4b20-a3ee-250de7fb1a9c
-- title:
--   One three negative integer restriction
-- statement:
--   Fixed-field version of the negative common-extension restriction.
-- source:
--   D1Bound5/OneThreeNegative.lean, lines 110-124, SHA-256 608590903d9651b83081c7c7b14962c497bd29944ae7411568eb23eee5734f08. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open scoped NumberField
open Module

namespace D1Bound5





















theorem _root_.D1Bound5.one_three_negative_integer_restriction {K : Type*} [Field K]
    [NumberField K] [NumberField.IsTotallyComplex K]
    (d : ℤ) (hd : 0 < d)
    (hparam : ∀ m : ℤ, m ≤ 0 → (∃ r : 𝓞 K, r*r = (m : 𝓞 K)) →
      ∃ y : ℤ, m = -d*y^2)
    {n : ℤ} (hn : n < 0)
    (hr : ∃ r : 𝓞 K, r*r = (n : 𝓞 K)+1)
    (hs : ∃ s : 𝓞 K, s*s = 3*(n : 𝓞 K)+1) :
    d=2 ∧ n%2=1 := by sorry










end D1Bound5
end
