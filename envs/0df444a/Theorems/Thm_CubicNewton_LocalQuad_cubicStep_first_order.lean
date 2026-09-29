-- Prove2me | Theorems.Thm_CubicNewton_LocalQuad_cubicStep_first_order
-- name    : CubicNewton.LocalQuad.cubicStep_first_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:34:40.958369+00:00
-- url     : https://prove2.me/theorems/55afa0ec-528a-4357-94aa-3dbdd50304c0
-- title:
--   Eq. (2.5): first-order condition satisfied by $T_M(x)$
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be twice differentiable with $L$-Lipschitz Hessian ($L > 0$), let $M > 0$, let $x \in \mathbb{R}^n$, and let $T = T_M(x)$ be any global minimizer of the cubic model
--   $$y \mapsto \langle f'(x), y - x\rangle + \tfrac12\langle f''(x)(y - x), y - x\rangle + \tfrac{M}{6}\|y - x\|^3 .$$
--   Then $T$ satisfies the system of nonlinear equations
--   $$f'(x) + f''(x)(T - x) + \tfrac12 M\,\|T - x\|\,(T - x) = 0 .$$
--
--   Equation (2.5) is the stationarity condition of the cubic model. It expresses the step as $T - x = -\big(f''(x) + \tfrac{M}{2}r_M(x) I\big)^{-1} f'(x)$ whenever the operator in brackets is invertible, which is the starting point of the local analysis.
--
--   **Formalization Note** $T_M(x)$ is represented by an arbitrary point satisfying `IsCubicStep` (a global minimizer). The mission takes $F = \mathbb{R}^n$ (standing assumptions on all of $\mathbb{R}^n$); the conclusion only uses $f'(x)$ and $f''(x)$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Section 2, Eq. (2.5)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

namespace CubicNewton.LocalQuad

/-- Nesterov–Polyak 2006, Section 2, Eq. (2.5), p. 182: every global minimizer `T = T_M(x)` of
the cubic model (with `M > 0`) satisfies `f′(x) + f″(x)(T − x) + ½M‖T − x‖·(T − x) = 0`.
Stated in the case `F = ℝⁿ`. -/
theorem cubicStep_first_order {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by sorry

end CubicNewton.LocalQuad
