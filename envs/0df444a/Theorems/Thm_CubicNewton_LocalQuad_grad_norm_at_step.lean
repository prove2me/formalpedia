-- Prove2me | Theorems.Thm_CubicNewton_LocalQuad_grad_norm_at_step
-- name    : CubicNewton.LocalQuad.grad_norm_at_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T21:35:27.802557+00:00
-- url     : https://prove2.me/theorems/3cbb6604-c918-46c7-9725-2d7ed47faa4d
-- title:
--   Lemma 3 (2.9): $\|f'(T_M(x))\| \le \frac12(L+M)r_M^2(x)$
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable with $L$-Lipschitz Hessian ($L > 0$), let $M > 0$ and $x \in \mathbb{R}^n$, let $T = T_M(x)$ be any global minimizer of the cubic model of $f$ at $x$ with parameter $M$, and let $r_M(x) = \|x - T_M(x)\|$. Then
--   $$\|f'(T_M(x))\| \le \tfrac12 (L + M)\, r_M^2(x).$$
--
--   The gradient at the new point is thus quadratically small in the step length; this is what makes the local convergence of the relaxed method quadratic.
--
--   **Formalization Note** The paper's hypothesis $T_M(x) \in F$ is automatic here because the mission takes $F = \mathbb{R}^n$, so it is dropped.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 183, Lemma 3, inequality (2.9)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Lemma 3, (2.9), p. 183, in the case `F = ℝⁿ` (so the hypothesis
`T_M(x) ∈ F` holds automatically): for every global minimizer `T = T_M(x)` of the cubic model
with `M > 0`, `‖f′(T)‖ ≤ ½(L + M) r_M(x)²` where `r_M(x) = ‖x − T‖`. -/
theorem grad_norm_at_step {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ‖g T‖ ≤ 1 / 2 * (L + M) * ‖x - T‖ ^ 2 := by sorry

end CubicNewton.LocalQuad
