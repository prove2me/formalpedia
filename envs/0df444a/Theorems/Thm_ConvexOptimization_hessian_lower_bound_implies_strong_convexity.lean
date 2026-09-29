-- Prove2me | Theorems.Thm_ConvexOptimization_hessian_lower_bound_implies_strong_convexity
-- name    : ConvexOptimization.hessian_lower_bound_implies_strong_convexity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:26:46.430307+00:00
-- url     : https://prove2.me/theorems/6f2485bd-1152-4c7b-8178-1814bfcd323a
-- title:
--   Hessian bound implies the quadratic lower bound
-- statement:
--   **A lower bound on the Hessian yields the quadratic lower bound on the function** — the implication (9.7) $\Rightarrow$ (9.8) of Boyd & Vandenberghe.
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice differentiable, with gradient field $g = \nabla f$ and Hessian field $H = \nabla^2 f$, where $H(x)$ is a continuous linear map on $\mathbb{R}^n$. Let $m \in \mathbb{R}$ and assume the uniform quadratic-form bound $\nabla^2 f(x) \succeq mI$, i.e.
--
--   $$m \lVert v\rVert_2^{2} \;\le\; \langle \nabla^2 f(x)\, v,\, v\rangle \qquad \text{for all } x, v \in \mathbb{R}^n .$$
--
--   Then for all $x, y \in \mathbb{R}^n$
--
--   $$f(y) \;\ge\; f(x) + \langle \nabla f(x), y - x\rangle + \frac{m}{2}\lVert y - x\rVert_2^{2} .$$
--
--   This is the bridge between the two ways of expressing strong convexity: the *pointwise* second-order condition that is easy to verify for a concrete objective, and the *global* quadratic lower bound that the convergence proofs actually consume. Applied with $m = 0$ it recovers the first-order characterization of convexity, and with $-M$ in place of $m$ (after replacing $f$ by $-f$) the matching smoothness upper bound.
--
--   **Formalization Note** The gradient and Hessian are explicit fields tied to $f$ by `∀ x, HasGradientAt f (g x) x` and `∀ x, HasFDerivAt g (H x) x`; the constant $m$ is an arbitrary real, not assumed positive, so the statement covers the convex ($m = 0$) case as well. Source: B&V §9.1.2 p. 459, eq. (9.8).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 459, §9.1.2 eq. (9.7)-(9.8) (strong convexity and the resulting quadratic lower bound)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.hessian_lower_bound_implies_strong_convexity {n : ℕ} (m : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  sorry
