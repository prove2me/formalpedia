-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_grad_inner_step_nonneg
-- name    : CubicNewton.Nonconvex.grad_inner_step_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:17:41.300993+00:00
-- url     : https://prove2.me/theorems/a7a2b82f-8f8f-4edd-b996-ce4ef2080a7d
-- title:
--   Lemma 2 (2.8): $\langle f'(x), x - T_M(x)\rangle \ge 0$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$. Assume the Hessian is Lipschitz continuous on $F$ in the spectral norm (Assumption 1): for some $L > 0$,
--   $$\|f''(x) - f''(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in F.$$
--
--   Let $x_0 \in \operatorname{int} F$ be a starting point such that $F$ contains the level set $\mathcal{L}(f(x_0)) = \{x \in \mathbb{R}^n : f(x) \le f(x_0)\}$ in its interior.
--
--   For $M > 0$ let $T = T_M(x)$ be **any global minimizer** over $y \in \mathbb{R}^n$ of the cubic model
--   $$\langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3,$$
--   and write $r_M(x) = \|x - T_M(x)\|$.
--
--   Then for any $x \in F$ with $f(x) \le f(x_0)$,
--   $$\langle f'(x),\, x - T_M(x)\rangle \ge 0 .$$
--   So the cubic step never moves uphill to first order. This is the first claim of Lemma 2; together with (2.6) it gives the model decrease of Lemma 4.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm. The step $T_M(x)$ is an arbitrary global minimizer of the cubic model (`IsCubicStep`), never a merely stationary point. The level-set hypothesis is written `{x | f x ≤ f x₀} ⊆ interior F`, for $f$ defined on all of $\mathbb{R}^n$ as in problem (3.1).
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Lemma 2, relation (2.8) (first claim of Lemma 2)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Lemma 2, relation (2.8), p. 182 (first claim of Lemma 2 only). -/
theorem grad_inner_step_nonneg {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hfx : f x ≤ f x₀)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := by sorry

end CubicNewton.Nonconvex
