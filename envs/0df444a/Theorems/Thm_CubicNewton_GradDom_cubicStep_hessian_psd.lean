-- Prove2me | Theorems.Thm_CubicNewton_GradDom_cubicStep_hessian_psd
-- name    : CubicNewton.GradDom.cubicStep_hessian_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:27:54.054985+00:00
-- url     : https://prove2.me/theorems/ef4d79e9-4398-4685-bfd8-41f01656490a
-- title:
--   Proposition 1 (2.7) — $f''(x) + \tfrac12 M r_M(x) I \succeq 0$
-- statement:
--   Under the standing assumptions, let $x \in F$, $M > 0$, and let $T = T_M(x)$ be any global minimizer of the cubic model at $x$, with $r_M(x) = \|x - T\|$. Then
--   $$f''(x) + \tfrac12 M\, r_M(x)\, I \succeq 0,$$
--   that is, $\langle f''(x) v, v\rangle + \frac12 M r_M(x) \|v\|^2 \ge 0$ for every $v \in \mathbb{R}^n$.
--   This second-order property of the global minimizer of the cubic model is what distinguishes it from a merely stationary point, and it is used in the proof of the model decrease (2.11).
--
--   **Formalization Note** Positive semidefiniteness is written as nonnegativity of the quadratic form.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Proposition 1, (2.7)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Proposition 1, (2.7), p. 182: `f″(x) + ½ M r_M(x) I ⪰ 0`, written as
nonnegativity of the quadratic form, where `r_M(x) = ‖x − T‖` for any global minimizer `T`. -/
theorem cubicStep_hessian_psd {n : ℕ}
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
    ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪H x v, v⟫ + 1 / 2 * M * ‖x - T‖ * ‖v‖ ^ 2 := by sorry

end CubicNewton.GradDom
