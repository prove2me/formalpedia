-- Prove2me | Theorems.Thm_CubicNewton_GradDom_run_decrease
-- name    : CubicNewton.GradDom.run_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:30:00.75629+00:00
-- url     : https://prove2.me/theorems/e4b8de5e-fdd4-4fd2-8b2f-290430ae2a35
-- title:
--   Lemma 7 (4.10) — decrease of $f$ along method (3.3) in terms of $\|f'(x_{k+1})\|^{3/2}$
-- statement:
--   Let $F \subseteq \mathbb{R}^n$ be closed and convex, $f$ twice differentiable on $F$ with $L$-Lipschitz Hessian ($L > 0$), and $x_0 \in \operatorname{int} F$ with $\{x : f(x) \le f(x_0)\} \subseteq \operatorname{int} F$. Let $0 < L_0 \le L$ and let $(x_k, M_k)_{k \ge 0}$ be any run of method (3.3) from $x_0$. Then for every $k \ge 0$
--   $$f(x_k) - f(x_{k+1}) \ge \frac{L_0\,\|f'(x_{k+1})\|^{3/2}}{3\sqrt2\,(L + L_0)^{3/2}} .$$
--   This is the auxiliary result through which the gradient-domination inequality enters the analysis of Theorem 7: it turns a lower bound on the gradient into a guaranteed decrease of the objective.
--
--   **Formalization Note** Fractional powers are `Real.rpow` of nonnegative numbers.
-- source:
--   Nesterov & Polyak, Cubic regularization of Newton method and its global performance, Math. Program. Ser. A 108 (2006) 177–205, DOI 10.1007/s10107-006-0706-8, p. 193, Lemma 7, inequality (4.10)

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicNewtonRun

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

/-- Nesterov–Polyak 2006, Lemma 7, inequality (4.10), p. 193: at each step of method (3.3),
`f(x_k) − f(x_{k+1}) ≥ L₀ ‖f′(x_{k+1})‖^{3/2} / (3√2 (L + L₀)^{3/2})` for every `k ≥ 0`. -/
theorem run_decrease {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (L₀ : ℝ) (hL₀ : 0 < L₀) (hL₀L : L₀ ≤ L)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (M : ℕ → ℝ) (hrun : CubicNewton.Shared.IsCubicNewtonRun f g H L₀ L x₀ x M) :
    ∀ k : ℕ, f (x k) - f (x (k + 1)) ≥
      L₀ * ‖g (x (k + 1))‖ ^ (3 / 2 : ℝ) / (3 * Real.sqrt 2 * (L + L₀) ^ (3 / 2 : ℝ)) := by sorry

end CubicNewton.GradDom
