-- Prove2me | Theorems.Thm_FatkhullinPolyak_HessStep_hessian_step_linear_rate
-- name    : FatkhullinPolyak.HessStep.hessian_step_linear_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:51:31.745252+00:00
-- url     : https://prove2.me/theorems/da2542cc-4200-4f8c-a229-f8fd4695dc1e
-- title:
--   Theorem 6.1 — the Hessian-step gradient method converges linearly: locally (6.3), and globally when damped (6.4)
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be a twice differentiable, $\mu$-strongly convex function ($\mu>0$) whose gradient $\nabla f$ is Lipschitz continuous with constant $L$ and whose Hessian $\nabla^2 f$ is Lipschitz continuous with constant $M$ (operator norm). Let $x_*$ be its global minimizer. Consider the gradient method (6.1)
--   $$
--   x_{j+1}=x_j-\gamma_j\nabla f(x_j),\qquad \gamma_j=\frac{\|\nabla f(x_j)\|^2}{\langle\nabla^2 f(x_j)\nabla f(x_j),\nabla f(x_j)\rangle}.
--   $$
--   Then:
--
--   1. **Local linear rate.** If $\delta>0$ and the initial point $x_0$ satisfies
--   $$
--   M\sqrt{2L\bigl(f(x_0)-f(x_*)\bigr)}\le 3\mu^2(1-\delta),\tag{6.2}
--   $$
--   then the iterates of (6.1) satisfy, for every $j\ge0$,
--   $$
--   f(x_j)-f(x_*)\le\bigl(f(x_0)-f(x_*)\bigr)\Bigl(1-\frac{\mu\delta}{L}\Bigr)^j.\tag{6.3}
--   $$
--   2. **Global linear rate of the damped method.** If $0<\sigma\le\mu/L$, then for every initial point $x_0$ the iterates of the damped method $x_{j+1}=x_j-\sigma\gamma_j\nabla f(x_j)$ satisfy, for every $j\ge0$,
--   $$
--   f(x_j)-f(x_*)\le\bigl(f(x_0)-f(x_*)\bigr)\Bigl(1-\frac{\mu\sigma}{L}\Bigr)^j.\tag{6.4}
--   $$
--
--   The step size of (6.1) uses one Hessian–vector product and no knowledge of $L$ or $\mu$. The theorem justifies it for nonquadratic strongly convex functions: linear convergence near the minimizer, and from any starting point once the step is damped by $\sigma\le\mu/L$.
--
--   **Formalization Note** Both claims share the hypotheses of the theorem as printed, including the Lipschitz Hessian, although the damped claim does not use $M$. The damping positivity $\sigma>0$ is implicit on the page and added. Condition (6.2) is a hypothesis on $x_0$ only. When $\delta>1$ it cannot hold (its left side is nonnegative), so claim 1 is then vacuous, as on the page. The minimizer is taken as a hypothesis ($f(x_*)\le f(y)$ for all $y$), not constructed. At a stationary iterate the step is $0/0=0$ in Lean, so the method stays at the minimizer and both bounds still hold. Strong convexity is Mathlib's `StrongConvexOn Set.univ μ f` (modulus $\frac{\mu}{2}\|x-y\|^2$). $L$ and $M$ are real constants in the Lipschitz inequalities $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ and $\|\nabla^2 f(x)-\nabla^2 f(y)\|\le M\|x-y\|$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 13, Theorem 6.1, Eqs. (6.1)-(6.4); proof in Appendix D.4, p. 19

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem hessian_step_linear_rate {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L M : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖)
    (hmin : ∀ y : EuclideanSpace ℝ (Fin n), f xstar ≤ f y) :
    (∀ (δ : ℝ) (x₀ : EuclideanSpace ℝ (Fin n)), 0 < δ →
        M * Real.sqrt (2 * L * (f x₀ - f xstar)) ≤ 3 * μ ^ 2 * (1 - δ) →
        ∀ j : ℕ, f (hessIter f x₀ j) - f xstar ≤ (f x₀ - f xstar) * (1 - μ * δ / L) ^ j) ∧
    (∀ σ : ℝ, 0 < σ → σ ≤ μ / L → ∀ (x₀ : EuclideanSpace ℝ (Fin n)) (j : ℕ),
        f (dampedHessIter f σ x₀ j) - f xstar ≤ (f x₀ - f xstar) * (1 - μ * σ / L) ^ j) := by sorry

end FatkhullinPolyak.HessStep
