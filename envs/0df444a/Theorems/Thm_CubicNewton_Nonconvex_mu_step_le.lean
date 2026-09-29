-- Prove2me | Theorems.Thm_CubicNewton_Nonconvex_mu_step_le
-- name    : CubicNewton.Nonconvex.mu_step_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:19:41.983168+00:00
-- url     : https://prove2.me/theorems/ad7e2ec3-eac4-4578-b3c9-f4a8d3b737b5
-- title:
--   Lemma 5: $\mu_M(T_M(x)) \le r_M(x)$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be a closed convex set with nonempty interior, and let $f$ be twice differentiable on $F$, with gradient $f'(x)$ and Hessian $f''(x)$. Assume the Hessian is Lipschitz continuous on $F$ in the spectral norm (Assumption 1): for some $L > 0$,
--   $$\|f''(x) - f''(y)\| \le L\,\|x - y\| \qquad \text{for all } x, y \in F.$$
--
--   For $M > 0$ let $T = T_M(x)$ be **any global minimizer** over $y \in \mathbb{R}^n$ of the cubic model
--   $$\langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3,$$
--   and write $r_M(x) = \|x - T_M(x)\|$.
--
--   For $M > 0$ the second-order optimality measure of Section 3 is
--   $$\mu_M(x) = \max\Big\{ \sqrt{\tfrac{2}{L + M}\,\|f'(x)\|},\ -\tfrac{2}{2L + M}\,\lambda_n(f''(x)) \Big\},$$
--   where $\lambda_n$ denotes the smallest eigenvalue. Then for any $x \in F$ with $T_M(x) \in F$,
--   $$\mu_M(T_M(x)) \le r_M(x) .$$
--   The optimality measure at the new point is bounded by the length of the step. Together with the summability of $r_{M_i}(x_i)^3$ this yields the rate of Theorem 1.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient and Hessian are given as maps `g` and `H` with `HasGradientAt f (g x) x` and `HasFDerivAt g (H x) x` at every `x ∈ F` (two-sided derivatives, also at boundary points of $F$); the operator norm on `H x` is the spectral norm. The step $T_M(x)$ is an arbitrary global minimizer of the cubic model (`IsCubicStep`), never a merely stationary point. $\lambda_n$ is `lamMin`, the Rayleigh-quotient infimum over the unit sphere (for $n = 0$ it is $0$). The hypothesis $T_M(x) \in F$ is added to the printed statement: the proof uses inequality (2.9), which assumes it, and the Lipschitz bound (2.1) between $x$ and $T_M(x)$. It holds at every iterate of method (3.3).
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 184, Lemma 5

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep
import Definitions.Def_CubicNewton_Nonconvex_muMeasure

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

/-- Nesterov–Polyak 2006, Lemma 5, p. 184: `μ_M(T_M(x)) ≤ r_M(x)`. The hypothesis
`T_M(x) ∈ F` is added: the printed proof uses (2.9) and the Lipschitz bound (2.1) at `T_M(x)`. -/
theorem mu_step_le {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hTF : T ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    muMeasure L M g H T ≤ ‖x - T‖ := by sorry

end CubicNewton.Nonconvex
