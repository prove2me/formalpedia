-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_ClosureClassQuadraticBound_parallel_class_card_quadratic_bound
-- name    : CountingMatroid.Analysis.ClosureClassQuadraticBound.parallel_class_card_quadratic_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:26:46.340871+00:00
-- url     : https://prove2.me/theorems/90c078a4-a1c3-4d89-868d-ac8368848494
-- title:
--   A sharp cardinality bound for discounted within-class pairs
-- statement:
--   Let $\alpha,\beta$ be types with decidable equality, let $T\subseteq\alpha$ be finite, let $f:\alpha\to\beta$ assign class labels, and let $q\in\mathbb R$ satisfy $0\le q\le1$. For $a,b\in T$, define $B_{aa}=0$, set $B_{ab}=q$ for distinct elements in the same class, and set $B_{ab}=1$ for elements in different classes. For every $y:\alpha\to\mathbb R$,
--
--   $$|T|\sum_{a,b\in T}B_{ab}y(a)y(b)\le(|T|-1)\left(\sum_{a\in T}y(a)\right)^2.$$
--
--   No sign condition is imposed on $y$, and the empty set is allowed. This controls the pair form using the number of labels.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ClosureClassQuadraticBound.lean#L62-L100

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

theorem CountingMatroid.Analysis.ClosureClassQuadraticBound.parallel_class_card_quadratic_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (y : α → ℝ) :
    (T.card : ℝ) * (∑ a ∈ T, ∑ b ∈ T,
      (if a = b then 0 else if f a = f b then q else 1) * y a * y b)
        ≤ ((T.card : ℝ) - 1) * (∑ a ∈ T, y a) ^ 2 := by sorry
