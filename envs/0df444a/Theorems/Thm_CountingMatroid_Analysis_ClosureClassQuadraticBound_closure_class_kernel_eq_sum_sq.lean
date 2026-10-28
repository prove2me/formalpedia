-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ClosureClassQuadraticBound_closure_class_kernel_eq_sum_sq
-- name    : CountingMatroid.Analysis.ClosureClassQuadraticBound.closure_class_kernel_eq_sum_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:44:06.138839+00:00
-- url     : https://prove2.me/theorems/a347fce9-ddf8-4610-8023-5b017afb26b2
-- title:
--   An equality kernel is a sum of squared fiber sums
-- statement:
--   Let $\alpha,\beta$ be types with decidable equality, let $T\subseteq\alpha$ be finite, let $f:\alpha\to\beta$ label classes, and let $u:\alpha\to\mathbb R$. Then
--
--   $$\sum_{a\in T}\sum_{b\in T}\mathbf1_{f(a)=f(b)}u(a)u(b)=\sum_{j\in f(T)}\left(\sum_{\substack{a\in T\\f(a)=j}}u(a)\right)^2.$$
--
--   This decomposition shows that the quadratic form of the equality-of-class kernel is positive semidefinite, with one square for each nonempty class.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ClosureClassQuadraticBound.lean#L14-L35

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
set_option autoImplicit false

/-! The quadratic correction indexed by equal closure classes is nonnegative:
it is a sum of squares of the sums within each class. -/

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ClosureClassQuadraticBound
open scoped BigOperators

theorem CountingMatroid.Analysis.ClosureClassQuadraticBound.closure_class_kernel_eq_sum_sq {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (u : α → ℝ) :
    (∑ a ∈ T, ∑ b ∈ T, if f a = f b then u a * u b else 0) =
      ∑ j ∈ T.image f, (∑ a ∈ T with f a = j, u a) ^ 2 := by sorry
