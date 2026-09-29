-- Prove2me | Theorems.Thm_FatkhullinPolyak_HessStep_cubic_taylor_bound
-- name    : FatkhullinPolyak.HessStep.cubic_taylor_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:49:28.905505+00:00
-- url     : https://prove2.me/theorems/3dd70e21-2b42-4789-a266-c55a821c6a76
-- title:
--   Appendix D.4 — cubic Taylor bound for a function with Lipschitz Hessian
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable, and suppose its Hessian is Lipschitz continuous with constant $M$ in the operator norm:
--   $$
--   \|\nabla^2 f(x)-\nabla^2 f(y)\|\le M\|x-y\|\quad\text{for all }x,y\in\mathbb{R}^n.
--   $$
--   Then the second-order Taylor expansion of $f$ has a cubic error bound: for all $x,y\in\mathbb{R}^n$,
--   $$
--   \Bigl|f(x+y)-f(x)-\langle\nabla f(x),y\rangle-\tfrac12\langle\nabla^2 f(x)y,y\rangle\Bigr|\le\frac{M}{6}\|y\|^3.
--   $$
--
--   This is the first display of the proof of Theorem 6.1 (Appendix D.4). Applied with $y=-\gamma_j\nabla f(x_j)$ it controls how far one step of the method (6.1) can deviate from the prediction of the quadratic model.
--
--   **Formalization Note** Twice differentiability is stated as differentiability of $f$ and of its Fréchet derivative at every point. The Hessian norm is the operator norm of $\nabla^2 f(x)$ as a continuous bilinear map (`fderiv ℝ (fderiv ℝ f) x`), which for the symmetric Hessian is its spectral norm, not the Frobenius norm.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 19, Appendix D.4 (proof of Theorem 6.1), first display

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem cubic_taylor_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖) :
    ∀ x y : EuclideanSpace ℝ (Fin n),
      |f (x + y) - f x - inner ℝ (gradient f x) y - (1 / 2) * hessQuad f x y| ≤ M / 6 * ‖y‖ ^ 3 := by sorry

end FatkhullinPolyak.HessStep
