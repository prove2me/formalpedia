-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_kkt_sufficient
-- name    : FirstOrderOpt.ConvexTheory.kkt_sufficient
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:56:03.362086+00:00
-- url     : https://prove2.me/theorems/e0a3cc39-cb86-41c1-8283-1705ce6a4d4f
-- title:
--   Theorem 2.8(a) — KKT conditions are sufficient for optimality
-- statement:
--   Let (2.3.16) be a convex program with $X$ convex, $f, g_1,\dots,g_m$ convex on $X$, and
--   $h_1,\dots,h_p$ affine. Let $x^*$ be a feasible point of (2.3.16) at which $f,
--   g_1,\dots,g_m$ are differentiable.
--
--   **Theorem 2.8(a).** If there exist Lagrange multipliers $\lambda^* \ge 0$ and $y^*$ such
--   that the KKT conditions
--   $$\nabla f(x^*) + \sum_{i=1}^m \lambda_i^* \nabla g_i(x^*) + \sum_{j=1}^p y_j^* \nabla
--   h_j(x^*) \in N_X^*(x^*) \quad \text{[stationarity]},$$
--   $$\lambda_i^* g_i(x^*) = 0,\ 1 \le i \le m \quad \text{[complementary slackness]}$$
--   hold (together with $x^*$'s primal feasibility, assumed above), then $x^*$ is optimal for
--   (2.3.16).
--
--   **Formalization Note.** $h_j$ affine is represented via witnesses $w_j, b_j$ with $h_j(x) =
--   \langle w_j,x\rangle + b_j$, so $\nabla h_j(x^*) = w_j$ is used directly in the stationarity
--   sum in place of a computed gradient. $N_X^*(x^*)$ is
--   `FirstOrderOpt.ConvexTheory.normalCone X xstar`. The gradient `∇` is Mathlib's
--   `Gradient.gradient`, well-defined (as `0`) even when $f$ is not differentiable at $x^*$, so
--   the differentiability hypotheses on $f, g_i$ at $x^*$ are stated explicitly rather than left
--   implicit.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 42, Theorem 2.8(a)

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

namespace FirstOrderOpt.ConvexTheory

open scoped Gradient

/-- Theorem 2.8(a) (KKT sufficiency). At a feasible, differentiable `x*` of the convex program
(2.3.16), if there are multipliers `λ* ≥ 0, y*` satisfying stationarity (the KKT gradient
combination lies in the normal cone of `X` at `x*`) and complementary slackness, then `x*` is
optimal. -/
theorem kkt_sufficient {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X)
    (hfdiff : DifferentiableAt ℝ f xstar) (hgdiff : ∀ i, DifferentiableAt ℝ (g i) xstar)
    (hxstar_g : ∀ i, g i xstar ≤ 0) (hxstar_h : ∀ j, h j xstar = 0)
    (lamStar : Fin m → ℝ) (yStar : Fin p → ℝ) (hlamStar : ∀ i, 0 ≤ lamStar i)
    (hstationarity : (∇ f xstar) + (∑ i, lamStar i • ∇ (g i) xstar) + (∑ j, yStar j • w j) ∈
      normalCone X xstar)
    (hcomplementary : ∀ i, lamStar i * g i xstar = 0) :
    ∀ x ∈ X, (∀ i, g i x ≤ 0) → (∀ j, h j x = 0) → f xstar ≤ f x := by sorry

end FirstOrderOpt.ConvexTheory
