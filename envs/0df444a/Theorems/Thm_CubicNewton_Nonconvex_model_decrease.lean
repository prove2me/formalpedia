-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_model_decrease
-- name    : CubicNewton.Nonconvex.model_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:18:16.529974+00:00
-- url     : https://prove2.me/theorems/6e3ed611-3454-4c3c-986e-0b31d1cadceb
-- title:
--   Lemma 4 (2.11): $f(x) - \bar f_M(x) \ge \frac{M}{12} r_M(x)^3$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$. Assume the Hessian is Lipschitz continuous on $F$ in the spectral norm (Assumption 1): for some $L > 0$,
--   $$\|f''(x) - f''(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in F.$$
--
--   For $M > 0$ let $T = T_M(x)$ be **any global minimizer** over $y \in \mathbb{R}^n$ of the cubic model
--   $$\langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3,$$
--   and write $r_M(x) = \|x - T_M(x)\|$.
--
--   Let $\bar f_M(x) = \min_y \big[f(x) + \langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3\big]$, the value of the regularized model at its minimizer $T_M(x)$. Then for any $x \in F$,
--   $$f(x) - \bar f_M(x) \ge \tfrac{M}{12}\, r_M(x)^3 .$$
--   Combined with the acceptance test $f(x_{k+1}) \le \bar f_{M_k}(x_k)$ of method (3.3), this is the per-iteration decrease that is summed in Theorem 1.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm. The step $T_M(x)$ is an arbitrary global minimizer of the cubic model (`IsCubicStep`), never a merely stationary point. $\bar f_M(x)$ is written as `f x + cubicModel g H M x T`, the model value at the global minimizer $T$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 183, Lemma 4, inequality (2.11)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Lemma 4, inequality (2.11), p. 183:
`f(x) − f̄_M(x) ≥ (M/12) r_M(x)³`, where `f̄_M(x) = f(x) + cubicModel g H M x T` for a global
minimizer `T` of the cubic model and `r_M(x) = ‖x − T‖`. -/
theorem model_decrease {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    f x - (f x + CubicNewton.Shared.cubicModel g H M x T) ≥ M / 12 * ‖x - T‖ ^ 3 := by sorry

end CubicNewton.Nonconvex
