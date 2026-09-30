-- Prove2me | Theorems.Thm_FatkhullinPolyak_HessStep_hessStep_one_step_bound
-- name    : FatkhullinPolyak.HessStep.hessStep_one_step_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:49:53.731674+00:00
-- url     : https://prove2.me/theorems/a9b2ed5f-fcf5-481e-b16a-13782896c726
-- title:
--   Appendix D.4 — one-step decrease of the Hessian-step gradient method (6.1)
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable and $\mu$-strongly convex with $\mu>0$, and let its Hessian be Lipschitz continuous with constant $M$ in the operator norm. For a point $x$ write $g=\nabla f(x)$ and let
--   $$
--   \gamma=\frac{\|g\|^2}{\langle\nabla^2 f(x)g,g\rangle}
--   $$
--   be the step size of the method (6.1). Then the next iterate $x^+=x-\gamma g$ satisfies
--   $$
--   f(x^+)\le f(x)-\frac12\gamma\|g\|^2\Bigl(1-\frac{M\gamma^2}{3}\|g\|\Bigr).
--   $$
--
--   In the notation of the paper, with $x=x_j$, $x^+=x_{j+1}$ and $\varphi_j=f(x_j)$, this is $\varphi_{j+1}\le\varphi_j-\frac12\gamma_j\|\nabla f(x_j)\|^2\bigl(1-\frac{M\gamma_j^2}{3}\|\nabla f(x_j)\|\bigr)$. It shows the method decreases $f$ as long as $M\gamma_j^2\|\nabla f(x_j)\|<3$, which is the basis of the local linear rate (6.3).
--
--   **Formalization Note** The page derives this display inside the proof of Theorem 6.1, whose standing hypotheses include $\mu$-strong convexity; it is kept here because the inequality uses $\gamma\ge 0$, which convexity guarantees. The Lipschitz constant of the gradient is not needed and is not assumed. At a stationary point $\gamma=0$ by Lean's convention $0/0=0$, and both sides equal $f(x)$. Strong convexity is Mathlib's `StrongConvexOn Set.univ μ f`, with modulus $\frac{\mu}{2}\|x-y\|^2$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 19, Appendix D.4 (proof of Theorem 6.1), third display

import Mathlib
import Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod

namespace FatkhullinPolyak.HessStep

theorem hessStep_one_step_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ M : ℝ)
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (fderiv ℝ f))
    (hμ : 0 < μ) (hconv : StrongConvexOn Set.univ μ f)
    (hM : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ M * ‖x - y‖)
    (x : EuclideanSpace ℝ (Fin n)) :
    f (x - hessStep f x • gradient f x) ≤
      f x - (1 / 2) * hessStep f x * ‖gradient f x‖ ^ 2 *
        (1 - M * hessStep f x ^ 2 / 3 * ‖gradient f x‖) := by sorry

end FatkhullinPolyak.HessStep
