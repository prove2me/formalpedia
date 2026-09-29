-- Prove2me | Theorems.Thm_CubicNewton_GradDom_model_decrease
-- name    : CubicNewton.GradDom.model_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:28:59.374974+00:00
-- url     : https://prove2.me/theorems/c0a11c1e-af99-4947-8490-ba406c71ea63
-- title:
--   Lemma 4 (2.11) — model decrease $f(x) - \bar f_M(x) \ge \tfrac{M}{12} r_M(x)^3$
-- statement:
--   Under the standing assumptions, let $x \in F$, $M > 0$, and let $T = T_M(x)$ be any global minimizer of the cubic model at $x$, with $r_M(x) = \|x - T\|$ and $\bar f_M(x) = f(x) + \min_y m_{M,x}(y)$. Then
--   $$f(x) - \bar f_M(x) \ge \frac{M}{12}\, r_M(x)^3 .$$
--   Combined with the acceptance test of method (3.3), this is the per-step decrease of the objective in terms of the step length.
--
--   **Formalization Note** $\bar f_M(x)$ is written as $f(x)$ plus the model evaluated at the minimizer $T$.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 183, Lemma 4, inequality (2.11)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

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

end CubicNewton.GradDom
