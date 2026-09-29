-- Prove2me | Theorems.Thm_CubicNewton_GradDom_cubicStep_first_order
-- name    : CubicNewton.GradDom.cubicStep_first_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:27:27.827278+00:00
-- url     : https://prove2.me/theorems/20827129-a66c-4f33-919d-1bc5c8132950
-- title:
--   Eq. (2.5) — first-order condition satisfied by $T_M(x)$
-- statement:
--   Under the standing assumptions of the paper (a closed convex $F \subseteq \mathbb{R}^n$ with non-empty interior, $f$ twice differentiable on $F$ with $L$-Lipschitz Hessian), let $x \in F$, $M > 0$, and let $T = T_M(x)$ be any global minimizer of the cubic model $y \mapsto \langle f'(x), y - x\rangle + \frac12\langle f''(x)(y-x), y-x\rangle + \frac M6\|y-x\|^3$. Then
--   $$f'(x) + f''(x)(T - x) + \tfrac12 M\,\|T - x\|\,(T - x) = 0 .$$
--   This is the stationarity condition of the cubic model at its minimizer; together with Proposition 1 it yields the model decrease (2.11) and the gradient bound (2.9).
--
--   **Formalization Note** The Hessian `H x` is not assumed self-adjoint; it is self-adjoint at points of $F$ because it is the derivative of a gradient and is continuous on $F$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Section 2, Eq. (2.5)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Section 2, Eq. (2.5), p. 182: every global minimizer `T = T_M(x)`
of the cubic model satisfies `f′(x) + f″(x)(T − x) + ½M‖T − x‖·(T − x) = 0`. -/
theorem cubicStep_first_order {n : ℕ}
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
    g x + H x (T - x) + (1 / 2 * M * ‖T - x‖) • (T - x) = 0 := by sorry

end CubicNewton.GradDom
