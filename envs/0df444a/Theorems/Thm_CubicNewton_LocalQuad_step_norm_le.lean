-- Prove2me | Theorems.Thm_CubicNewton_LocalQuad_step_norm_le
-- name    : CubicNewton.LocalQuad.step_norm_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:35:53.186536+00:00
-- url     : https://prove2.me/theorems/b38f2f93-65f0-45aa-bd7d-08bdea1a178d
-- title:
--   Eq. (3.9): $r_M(x) \le \|f'(x)\|/\lambda_n(f''(x))$ when $f''(x) \succ 0$
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable with $L$-Lipschitz Hessian ($L > 0$). Let $x \in \mathbb{R}^n$ be a point with $f''(x) \succ 0$, i.e. $\lambda_n(f''(x)) > 0$, let $M > 0$, and let $T = T_M(x)$ be any global minimizer of the cubic model of $f$ at $x$ with parameter $M$. Then
--   $$r_M(x) = \|T_M(x) - x\| \le \frac{\|f'(x)\|}{\lambda_n(f''(x))} .$$
--
--   In the paper this is the middle step of (3.9), $r_M(x) = \|(f''(x) + r_M(x)\tfrac{M}{2}I)^{-1} f'(x)\|$, followed by this bound: the step of the cubic-regularized method is never longer than the gradient norm divided by the smallest Hessian eigenvalue. It controls the change of the Hessian from one iterate to the next in the proof of Theorem 3.
--
--   **Formalization Note** In the paper (3.9) appears inside the proof of Theorem 3 for an iterate $x_k$ under the running assumption $\delta_k \le 1/4$; that assumption is not needed for the inequality and is not included. $\lambda_n$ is `lamMin`; $F = \mathbb{R}^n$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 187, Section 3, Eq. (3.9) (proof of Theorem 3)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep
import Definitions.Def_CubicNewton_Shared_lamMin

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Section 3, Eq. (3.9), p. 187 (proof of Theorem 3), in the case
`F = ℝⁿ`: if `f″(x) ≻ 0` (i.e. `λₙ(f″(x)) > 0`), `M > 0` and `T = T_M(x)` is a global
minimizer of the cubic model at `x`, then `r_M(x) = ‖T − x‖ ≤ ‖f′(x)‖ / λₙ(f″(x))`. -/
theorem step_norm_le {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hpos : 0 < CubicNewton.Shared.lamMin (H x)) (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖T - x‖ ≤ ‖g x‖ / CubicNewton.Shared.lamMin (H x) := by sorry

end CubicNewton.LocalQuad
