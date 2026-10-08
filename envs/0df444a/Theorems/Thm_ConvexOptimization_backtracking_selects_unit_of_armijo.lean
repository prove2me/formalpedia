-- Prove2me | Theorems.Thm_ConvexOptimization_backtracking_selects_unit_of_armijo
-- name    : ConvexOptimization.backtracking_selects_unit_of_armijo
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-15T08:29:31.516111+00:00
-- url     : https://prove2.me/theorems/2311d7b8-0b76-4859-85be-b51665de99d4
-- title:
--   Unit Armijo trial prevents backtracking
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ have a field $g$ satisfying the global first-order convexity inequality
--
--   $$
--   f(u)+\langle g(u),v-u\rangle\le f(v) \qquad (u,v\in\mathbb{R}^n).
--   $$
--
--   Fix $\beta\in(0,1)$ and a direction $\Delta$ at $x$. Suppose $t$ is the step returned by backtracking, represented by `IsBacktrackingStep`, and suppose the unit step already satisfies the Armijo condition
--
--   $$
--   f(x+\Delta)\le f(x)+\alpha\langle g(x),\Delta\rangle.
--   $$
--
--   Then $t=1$.
--
--   This isolates the full-step-selection fact used when Newton's method enters its quadratic phase. Convexity makes the Armijo acceptance set downward closed on $[0,1]$, so a successful unit trial prevents any backtracking.
--
--   **Formalization Note** The theorem bridges the local predecessor-failure clause in `IsBacktrackingStep` with the algorithmic fact that backtracking starts at one.
-- source:
--   Boyd and Vandenberghe, Convex Optimization, Cambridge University Press, 2004 (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf, section 9.2, p. 466 (backtracking starts at t=1 and stops at the first Armijo step), and section 9.5.3, p. 491 (the quadratic phase accepts the unit Newton step).

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.backtracking_selects_unit_of_armijo {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hfirst : ∀ u v, f u + ⟪g u, v - u⟫ ≤ f v)
    (ht : IsBacktrackingStep f g α β x Δ t)
    (hunit : f (x + Δ) ≤ f x + α * ⟪g x, Δ⟫) :
    t = 1 := by
  sorry
