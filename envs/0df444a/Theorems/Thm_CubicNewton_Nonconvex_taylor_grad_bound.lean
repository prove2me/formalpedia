-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_taylor_grad_bound
-- name    : CubicNewton.Nonconvex.taylor_grad_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:15:57.793974+00:00
-- url     : https://prove2.me/theorems/f3399ce5-4d2d-4a73-b52e-62befa4906c6
-- title:
--   Lemma 1 (2.2): $\|f'(y) - f'(x) - f''(x)(y-x)\| \le \frac12 L\|y-x\|^2$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$. Assume the Hessian is Lipschitz continuous on $F$ in the spectral norm (Assumption 1): for some $L > 0$,
--   $$\|f''(x) - f''(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in F.$$
--
--   Then for any $x$ and $y$ in $F$,
--   $$\|f'(y) - f'(x) - f''(x)(y - x)\| \le \tfrac12 L\,\|y - x\|^2 .$$
--   This is the first-order Taylor bound for the gradient under a Lipschitz Hessian. It gives the bound on $\|f'(T_M(x))\|$ in Lemma 3 and hence the gradient part of the rate in Theorem 1.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 181, Lemma 1, inequality (2.2)

import Mathlib


open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Lemma 1, inequality (2.2), p. 181. -/
theorem taylor_grad_bound {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ F, ∀ y ∈ F, ‖g y - g x - H x (y - x)‖ ≤ 1 / 2 * L * ‖y - x‖ ^ 2 := by sorry

end CubicNewton.Nonconvex
