-- Prove2me | Theorems.Thm_FatkhullinPolyak_HessStep_damped_step_descent
-- name    : FatkhullinPolyak.HessStep.damped_step_descent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:50:57.928307+00:00
-- url     : https://prove2.me/theorems/7de8ddbf-460f-42b0-9021-b908c20f943f
-- title:
--   (D.2) — one damped Hessian step decreases f by (σγ/2)‖∇f‖²
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable and $\mu$-strongly convex with $\mu>0$, with $L$-Lipschitz gradient, and let the damping factor satisfy $0<\sigma\le\mu/L$. For a point $x$ let $\gamma=\|\nabla f(x)\|^2/\langle\nabla^2 f(x)\nabla f(x),\nabla f(x)\rangle$ be the step size of (6.1), and let $x^+=x-\sigma\gamma\nabla f(x)$ be one step of the damped method. Then
--   $$
--   f(x^+)\le f(x)-\frac{\sigma\gamma}{2}\,\|\nabla f(x)\|^2.
--   $$
--
--   This is the conclusion of the chain (D.2), with $x=x_j$ and $x^+=x_{j+1}$. Combined with $\gamma\ge 1/L$ and strong convexity it gives the global linear rate (6.4) of the damped method.
--
--   **Formalization Note** The positivity $\sigma>0$ is not written on the page; it is implicit in calling $\sigma\gamma_j$ a damped step, and is added as a hypothesis. At a stationary point $\gamma=0$ (Lean's $0/0=0$) and both sides equal $f(x)$. Conventions for strong convexity, smoothness and the Hessian form are those of (D.1).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 19, Appendix D.4, Eq. (D.2) (final inequality)

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem damped_step_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L σ : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hσ : 0 < σ) (hσL : σ ≤ μ / L)
    (x : EuclideanSpace ℝ (Fin n)) :
    f (x - (σ * hessStep f x) • gradient f x) ≤
      f x - σ * hessStep f x / 2 * ‖gradient f x‖ ^ 2 := by sorry

end FatkhullinPolyak.HessStep
