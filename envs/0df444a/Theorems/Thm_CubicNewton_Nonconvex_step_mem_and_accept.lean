-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_step_mem_and_accept
-- name    : CubicNewton.Nonconvex.step_mem_and_accept
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:18:42.739794+00:00
-- url     : https://prove2.me/theorems/f37b3c8f-45fc-4442-8e6f-487cde31632a
-- title:
--   Lemma 4 (2.12): for $M \ge L$, $T_M(x) \in F$ and $f(T_M(x)) \le \bar f_M(x)$
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
--   Let $\bar f_M(x)$ be the minimum value of $f(x)$ plus the cubic model. If $M \ge L$, then for every $x \in \operatorname{int} F$ with $f(x) \le f(x_0)$,
--   $$T_M(x) \in F \qquad\text{and}\qquad f(T_M(x)) \le \bar f_M(x).$$
--   This shows that the acceptance test of method (3.3) is always passed by $M_k = L$, so the method is well defined whenever $L$ is known.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm. The step $T_M(x)$ is an arbitrary global minimizer of the cubic model (`IsCubicStep`), never a merely stationary point. The level-set hypothesis is written `{x | f x ≤ f x₀} ⊆ interior F`, for $f$ defined on all of $\mathbb{R}^n$ as in problem (3.1). The paper prints (2.12) under "for any $x \in F$"; its proof invokes the second claim of Lemma 2, which assumes $x \in \operatorname{int} F$, and the inclusion $\mathcal{L}(f(x)) \subseteq F$, which uses $f(x) \le f(x_0)$. Both are stated as hypotheses here. Every iterate of method (3.3) satisfies them.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 183, Lemma 4, (2.12) (proof via Lemma 2, p. 182)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Lemma 4, (2.12), p. 183: if `M ≥ L` then `T_M(x) ∈ F` and
`f(T_M(x)) ≤ f̄_M(x)`. Stated, as its proof via Lemma 2 requires, for `x ∈ int F` with
`f(x) ≤ f(x₀)`. -/
theorem step_mem_and_accept {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hLM : L ≤ M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior F)
    (hfx : f x ≤ f x₀) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    T ∈ F ∧ f T ≤ f x + CubicNewton.Shared.cubicModel g H M x T := by sorry

end CubicNewton.Nonconvex
