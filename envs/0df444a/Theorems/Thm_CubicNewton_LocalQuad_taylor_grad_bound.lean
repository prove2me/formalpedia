-- Prove2me | Theorems.Thm_CubicNewton_LocalQuad_taylor_grad_bound
-- name    : CubicNewton.LocalQuad.taylor_grad_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:33:25.89976+00:00
-- url     : https://prove2.me/theorems/9f9446cf-6923-4555-a36d-180a1edabb8c
-- title:
--   Lemma 1 (2.2): $\|f'(y)-f'(x)-f''(x)(y-x)\| \le \frac12 L\|y-x\|^2$
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable, with gradient $f'$ and Hessian $f''$, and suppose the Hessian is Lipschitz continuous with constant $L > 0$:
--   $$\|f''(x) - f''(y)\| \le L\|x - y\| \quad \text{for all } x, y \in \mathbb{R}^n,$$
--   where $\|\cdot\|$ on operators is the spectral norm. Then for all $x, y \in \mathbb{R}^n$
--   $$\|f'(y) - f'(x) - f''(x)(y - x)\| \le \tfrac12 L\|y - x\|^2 .$$
--
--   This is the first-order Taylor bound for the gradient under a Lipschitz Hessian. In the local analysis it bounds the gradient at the new iterate (Lemma 3).
--
--   **Formalization Note** The paper states the lemma for $x, y$ in a closed convex set $F$; this mission takes $F = \mathbb{R}^n$, with $f$ twice differentiable and Assumption 1 holding on all of $\mathbb{R}^n$. The gradient and Hessian are maps `g`, `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every point.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 181, Lemma 1, inequality (2.2)

import Mathlib

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Lemma 1, inequality (2.2), p. 181, in the case `F = ℝⁿ`:
if `f` is twice differentiable on `ℝⁿ` with `L`-Lipschitz Hessian, then for all `x, y`,
`‖f′(y) − f′(x) − f″(x)(y − x)‖ ≤ ½ L ‖y − x‖²`. -/
theorem taylor_grad_bound {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by sorry

end CubicNewton.LocalQuad
