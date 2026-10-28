-- Prove2me | Theorems.Thm_D1Bound5_norm_sq_eq_absolute_norm
-- name    : D1Bound5.norm_sq_eq_absolute_norm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:17.862527+00:00
-- url     : https://prove2.me/theorems/d2234fd9-57d9-47b5-b506-fffd58eda91e
-- title:
--   Norm sq eq absolute norm
-- statement:
--   The absolute algebraic norm is the squared modulus at every complex embedding of an imaginary quadratic field.
-- source:
--   D1Bound5/NormCompatibility.lean, lines 22-31, SHA-256 ef1bc04a6eec114fae40046f467c1e7234d97ebfd0fa13e3d1b6a5f362c2852a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5






theorem _root_.D1Bound5.norm_sq_eq_absolute_norm {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (hK : finrank ℚ K = 2) (φ : K →+* ℂ) (x : 𝓞 K) :
    ‖φ (x : K)‖^2 = (Algebra.norm ℤ x : ℝ) := by sorry

end D1Bound5
end
