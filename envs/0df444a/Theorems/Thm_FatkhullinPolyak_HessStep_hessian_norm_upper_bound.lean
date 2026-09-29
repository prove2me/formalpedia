-- Prove2me | Theorems.Thm_FatkhullinPolyak_HessStep_hessian_norm_upper_bound
-- name    : FatkhullinPolyak.HessStep.hessian_norm_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:50:18.652747+00:00
-- url     : https://prove2.me/theorems/f25868fd-d5c8-4352-8b62-6e54b6ca3c7b
-- title:
--   (D.1) — upper bound in the local Hessian norm for strongly convex, L-smooth functions
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable and $\mu$-strongly convex with $\mu>0$, and let its gradient be Lipschitz continuous with constant $L$:
--   $$
--   \|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|\quad\text{for all }x,y.
--   $$
--   Write $\|v\|^2_{\nabla^2 f(x)}=\langle\nabla^2 f(x)v,v\rangle$ for the local Hessian norm. Then for all $x,y\in\mathbb{R}^n$,
--   $$
--   f(y)\le f(x)+\langle\nabla f(x),y-x\rangle+\frac{L}{2\mu}\,\|y-x\|^2_{\nabla^2 f(x)}.
--   $$
--
--   This is inequality (D.1). It replaces the usual quadratic upper bound of an $L$-smooth function by one measured in the Hessian's own geometry, at the price of the condition number $L/\mu$. It is what makes the damped version of (6.1) converge from every starting point.
--
--   **Formalization Note** "$L$-smooth" is the Lipschitz continuity of $\nabla f$ with constant $L$ in the Euclidean norm, stated with a real constant $L$. Strong convexity is Mathlib's `StrongConvexOn Set.univ μ f`, with modulus $\frac{\mu}{2}\|x-y\|^2$. Twice differentiability is differentiability of $f$ and of its Fréchet derivative everywhere; the Hessian quadratic form is `fderiv ℝ (fderiv ℝ f) x v v`.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 19, Appendix D.4, Eq. (D.1)

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem hessian_norm_upper_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ L : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hL : ∀ x y : EuclideanSpace ℝ (Fin n), ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + L / (2 * μ) * hessQuad f x (y - x) := by sorry

end FatkhullinPolyak.HessStep
