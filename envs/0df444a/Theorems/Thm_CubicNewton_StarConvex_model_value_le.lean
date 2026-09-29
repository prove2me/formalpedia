-- Prove2me | Theorems.Thm_CubicNewton_StarConvex_model_value_le
-- name    : CubicNewton.StarConvex.model_value_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:24:10.390318+00:00
-- url     : https://prove2.me/theorems/92219698-fd88-42a9-bc32-6c1634f63f04
-- title:
--   Lemma 4 (2.10): $\bar f_M(x)\le\min_{y\in F}[f(y)+\tfrac{L+M}{6}\|y-x\|^3]$
-- statement:
--   Work under the standing assumptions of Section 2: $F \subseteq \mathbb{R}^n$ is closed and convex with nonempty interior, $f$ is twice differentiable on $F$ with gradient $f'$ and Hessian $f''$, and the Hessian is $L$-Lipschitz on $F$ with $L > 0$. Let $M > 0$, let $x \in F$, and let $T = T_M(x)$ be any global minimizer of the cubic model
--
--   $$m_{M,x}(y) = \langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3 ,$$
--
--   so that the model value is $\bar f_M(x) = f(x) + m_{M,x}(T)$. Then
--
--   $$\bar f_M(x) \le f(y) + \frac{L + M}{6}\,\|y - x\|^3 \qquad \text{for every } y \in F,$$
--
--   that is, $\bar f_M(x) \le \min_{y \in F}\big[f(y) + \tfrac{L+M}{6}\|y - x\|^3\big]$.
--
--   Combined with the acceptance test of method (3.3), this bounds the new function value by a minimum over $F$ of a regularized objective, which is the starting point of every global rate in Section 4.
--
--   **Formalization Note** The minimum over $y \in F$ is stated as a bound for every $y \in F$, which is equivalent. $\bar f_M(x)$ is written as $f(x)$ plus the model value at the chosen minimizer $T$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 183, Lemma 4, inequality (2.10)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.StarConvex

/-- Nesterov–Polyak 2006, Lemma 4, inequality (2.10), p. 183: under the standing assumptions of
Section 2, for any `x ∈ F` and any positive parameter `M`, let `T = T_M(x)` be a global minimizer
of the cubic model (2.4), so that `f̄_M(x) = f(x) + cubicModel g H M x T`. Then for every `y ∈ F`,
`f̄_M(x) ≤ f(y) + ((L + M)/6)‖y − x‖³`, i.e. `f̄_M(x) ≤ min_{y ∈ F} [f(y) + ((L + M)/6)‖y − x‖³]`. -/
theorem model_value_le {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L M : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ∀ y ∈ F, f x + CubicNewton.Shared.cubicModel g H M x T ≤ f y + (L + M) / 6 * ‖y - x‖ ^ 3 := by sorry

end CubicNewton.StarConvex
