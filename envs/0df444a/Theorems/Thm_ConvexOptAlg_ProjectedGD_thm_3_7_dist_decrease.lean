-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_thm_3_7_dist_decrease
-- name    : ConvexOptAlg.ProjectedGD.thm_3_7_dist_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:13:30.844004+00:00
-- url     : https://prove2.me/theorems/0b41af5c-8127-4d53-ab3d-1ab3b51b8eb5
-- title:
--   Proof of Theorem 3.7, p. 271 — g_X(x_s)ᵀ(x_s − x*) ≥ ‖g_X(x_s)‖²/(2β) and ‖x_{s+1} − x*‖ ≤ ‖x_s − x*‖
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, $f$ convex and $\beta$-smooth on $\mathcal X$ with $\beta>0$, and $x^*\in\mathcal X$ a minimizer of $f$ on $\mathcal X$. Let $(x_t)_{t\ge1}$ be a run of projected gradient descent with step size $\eta=1/\beta$, and write $g_{\mathcal X}(x_s)=\beta(x_s-x_{s+1})$. Then for every $s\ge1$,
--   $$g_{\mathcal X}(x_s)^\top(x_s-x^*)\ge\frac1{2\beta}\|g_{\mathcal X}(x_s)\|^2
--   \qquad\text{and}\qquad
--   \|x_{s+1}-x^*\|^2\le\|x_s-x^*\|^2 .$$
--
--   The distance of the iterates to the minimizer is non-increasing. This is the step that lets the proof of Theorem 3.7 replace $\|x_s-x^*\|$ by $\|x_1-x^*\|$ in the gap bound.
--
--   **Formalization Note** The run is `IsProjGDRun X g β x` (iterates from index $1$). The existence of a minimizer is the book's standing assumption; $\beta>0$ is implicit in the step $1/\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.7, p. 271 (last paragraph)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

namespace ConvexOptAlg.ProjectedGD

/-- The last paragraph of the proof of Theorem 3.7 (Bubeck, arXiv:1405.4980v2, p. 271): for a run
`(x_s)` of projected gradient descent with `η = 1/β` on a convex `β`-smooth `f` over a compact
convex `X`, with `x*` a minimizer of `f` on `X` and `s ≥ 1`,
`g_X(x_s)ᵀ(x_s − x*) ≥ (1/(2β))‖g_X(x_s)‖²` and `‖x_{s+1} − x*‖² ≤ ‖x_s − x*‖²`,
where `g_X(x_s) = β(x_s − x_{s+1})`. -/
theorem thm_3_7_dist_decrease {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothOn X f g β)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsProjGDRun X g β x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (s : ℕ) (hs : 1 ≤ s) :
    1 / (2 * β) * ‖gradMap β (x s) (x (s + 1))‖ ^ 2 ≤ ⟪gradMap β (x s) (x (s + 1)), x s - xstar⟫_ℝ ∧
      ‖x (s + 1) - xstar‖ ^ 2 ≤ ‖x s - xstar‖ ^ 2 := by sorry

end ConvexOptAlg.ProjectedGD
