-- Prove2me | Theorems.Thm_CubicNewton_GradDom_grad_inner_step_nonneg
-- name    : CubicNewton.GradDom.grad_inner_step_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:28:27.308858+00:00
-- url     : https://prove2.me/theorems/28ecdd4c-27dc-4082-9297-ddda779f4f70
-- title:
--   Lemma 2 (2.8) — $\langle f'(x), x - T_M(x)\rangle \ge 0$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be closed and convex, $f$ twice differentiable on $F$ with $L$-Lipschitz Hessian, and let $x_0 \in \operatorname{int} F$ be such that the level set $\{x : f(x) \le f(x_0)\}$ lies in $\operatorname{int} F$. Let $M > 0$, let $x \in F$ with $f(x) \le f(x_0)$, and let $T = T_M(x)$ be any global minimizer of the cubic model at $x$. Then
--   $$\langle f'(x),\, x - T\rangle \ge 0 .$$
--   The step $T_M(x) - x$ is therefore never an ascent direction. This is the first of the two claims of Lemma 2.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 182, Lemma 2, relation (2.8) (first claim)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Lemma 2, relation (2.8), p. 182 (first claim of Lemma 2 only):
for `x ∈ F` with `f(x) ≤ f(x₀)`, `⟨f′(x), x − T_M(x)⟩ ≥ 0`. -/
theorem grad_inner_step_nonneg {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hfx : f x ≤ f x₀)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := by sorry

end CubicNewton.GradDom
