-- Prove2me | Theorems.Thm_ConvexOptimization_local_min_is_global_min
-- name    : ConvexOptimization.local_min_is_global_min
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:31:09.955023+00:00
-- url     : https://prove2.me/theorems/15ddc197-cc86-489a-a2ae-5df5077f948e
-- title:
--   Local minima of convex functions are global
-- statement:
--   **A local minimum of a convex function is a global minimum.**
--
--   Let $X \subseteq \mathbb{R}^n$ and let $f$ be convex on $X$. Suppose $x \in X$ is a local minimum of $f$ on $X$: there is a radius $r > 0$ such that
--
--   $$f(x) \le f(y) \qquad \text{for every } y \in X \text{ with } \lVert y - x\rVert_2 < r .$$
--
--   Then $x$ minimizes $f$ over all of $X$.
--
--   This is the structural fact that makes convex optimization tractable: there are no strictly local traps, so any method that certifies local optimality certifies global optimality, and the words "optimal" and "locally optimal" can be used interchangeably throughout the theory. Convexity of $X$ itself is not needed as a separate hypothesis — it is carried by `ConvexOn ℝ X f`, which asserts convexity of the domain along with the inequality.
--
--   **Formalization Note** The conclusion is Mathlib's `IsMinOn f X x`; the local hypothesis is stated with an explicit radius rather than with a neighbourhood filter, matching the book's phrasing. Source: B&V §4.2.2, p. 138.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 138, §4.2.2 (any locally optimal point of a convex problem is globally optimal)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.local_min_is_global_min {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ X f) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hloc : ∃ r > 0, ∀ y ∈ X, ‖y - x‖ < r → f x ≤ f y) :
    IsMinOn f X x := by
  sorry
