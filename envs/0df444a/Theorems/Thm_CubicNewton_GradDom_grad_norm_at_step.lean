-- Prove2me | Theorems.Thm_CubicNewton_GradDom_grad_norm_at_step
-- name    : CubicNewton.GradDom.grad_norm_at_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:29:29.704153+00:00
-- url     : https://prove2.me/theorems/31560a88-bb25-41bd-8889-0ff61857c93f
-- title:
--   Lemma 3 (2.9) — $\|f'(T_M(x))\| \le \tfrac12(L+M) r_M(x)^2$
-- statement:
--   Under the standing assumptions, let $x \in F$, $M > 0$, and let $T = T_M(x)$ be any global minimizer of the cubic model at $x$ with $T \in F$. Then
--   $$\|f'(T)\| \le \tfrac12 (L + M)\, r_M(x)^2, \qquad r_M(x) = \|x - T\| .$$
--   The gradient at the new point is controlled by the square of the step length; Lemma 7 combines this with (2.11).
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 183, Lemma 3, inequality (2.9)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Lemma 3, (2.9), p. 183: if `T_M(x) ∈ F` then
`‖f′(T_M(x))‖ ≤ ½(L + M) r_M(x)²`. -/
theorem grad_norm_at_step {n : ℕ}
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
    ‖g T‖ ≤ 1 / 2 * (L + M) * ‖x - T‖ ^ 2 := by sorry

end CubicNewton.GradDom
