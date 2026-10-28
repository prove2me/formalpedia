-- Prove2me | Theorems.Thm_D1Bound5_IsD1_one_three_small_third_eq_eight
-- name    : D1Bound5.IsD1.one_three_small_third_eq_eight
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:37.287068+00:00
-- url     : https://prove2.me/theorems/e2885951-7a8a-45be-8840-fb36523bb496
-- title:
--   Is D1 — one three small third eq eight
-- statement:
--   In any actual full ring, a D(1)-set of cardinality at least five containing 1 and 3 has exactly the third candidate 8 below modulus 15. The accepted negative-extension theorem supplies positivity and rationality.
-- source:
--   D1Bound5/OneThreeEight.lean, lines 17-43, SHA-256 60602e3caf285e30e5c1611b6c08cecf7eefe23af11cee872a9962bf384b646f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
open scoped NumberField Classical
open Module

namespace D1Bound5




theorem _root_.D1Bound5.IsD1.one_three_small_third_eq_eight
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {A : Finset (𝓞 K)} (hA : IsD1 A)
    (h1 : (1 : 𝓞 K) ∈ A) (h3 : (3 : 𝓞 K) ∈ A) (hcard : 4 < A.card)
    (z : 𝓞 K) (hz : z ∈ A) (hz1 : z ≠ 1) (hz3 : z ≠ 3)
    (hlo : 9 ≤ ‖phi (z : K)‖^2) (hhi : ‖phi (z : K)‖^2 < 225) : z = 8 := by sorry



end D1Bound5
end
