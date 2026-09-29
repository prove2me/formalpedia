-- Prove2me | Theorems.Thm_CubicNewton_GradDom_taylor_grad_bound
-- name    : CubicNewton.GradDom.taylor_grad_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:26:53.41833+00:00
-- url     : https://prove2.me/theorems/47ce260e-5f56-4655-b764-04a4116a14c5
-- title:
--   Lemma 1 (2.2) — Taylor bound for the gradient under a Lipschitz Hessian
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with non-empty interior, and let $f$ be twice differentiable on $F$ with gradient $f'$ and Hessian $f''$. Assume the Hessian is Lipschitz on $F$ with constant $L > 0$ in the spectral norm: $\|f''(x) - f''(y)\| \le L\|x - y\|$ for all $x, y \in F$. Then for all $x, y \in F$
--   $$\|f'(y) - f'(x) - f''(x)(y - x)\| \le \tfrac12 L\,\|y - x\|^2 .$$
--   This is the first-order Taylor estimate for the gradient; Lemma 3 below applies it at $y = T_M(x)$.
--
--   **Formalization Note** $f'$ and $f''$ are maps `g`, `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every $x \in F$ (two-sided derivatives, also at boundary points of $F$).
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 181, Lemma 1, inequality (2.2)

import Mathlib

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Lemma 1, inequality (2.2), p. 181: for all `x, y ∈ F`,
`‖f′(y) − f′(x) − f″(x)(y − x)‖ ≤ ½ L ‖y − x‖²`. -/
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

end CubicNewton.GradDom
