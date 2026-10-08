-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_thm_3_7_descent_gap
-- name    : ConvexOptAlg.ProjectedGD.thm_3_7_descent_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:13:10.654131+00:00
-- url     : https://prove2.me/theorems/88ea674d-d3ea-4e20-8c0b-aa0d958c32e4
-- title:
--   Proof of Theorem 3.7, pp. 270–271 — f(x_{s+1}) − f(x_s) ≤ −‖g_X(x_s)‖²/(2β) and f(x_{s+1}) − f(x*) ≤ ‖g_X(x_s)‖·‖x_s − x*‖
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, $f$ convex and $\beta$-smooth on $\mathcal X$ with $\beta>0$, and $x^*\in\mathcal X$ a minimizer of $f$ on $\mathcal X$. Let $(x_t)_{t\ge1}$ be a run of projected gradient descent with step size $\eta=1/\beta$, and write $g_{\mathcal X}(x_s)=\beta(x_s-x_{s+1})$. Then for every $s\ge1$,
--   $$f(x_{s+1})-f(x_s)\le-\frac1{2\beta}\|g_{\mathcal X}(x_s)\|^2
--   \qquad\text{and}\qquad
--   f(x_{s+1})-f(x^*)\le\|g_{\mathcal X}(x_s)\|\cdot\|x_s-x^*\| .$$
--
--   These are the two displays with which the proof of Theorem 3.7 opens: the method is a descent method, and the optimality gap after a step is bounded by the size of the gradient mapping times the current distance to the optimum.
--
--   **Formalization Note** The run is `IsProjGDRun X g β x` (iterates from index $1$). The existence of a minimizer $x^*$ is the book's standing assumption (p. 242); $\beta>0$ is implicit in the step $1/\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.7, pp. 270–271 (first two displays)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

namespace ConvexOptAlg.ProjectedGD

/-- The two displays opening the proof of Theorem 3.7 (Bubeck, arXiv:1405.4980v2, pp. 270–271),
for a run `(x_s)` of projected gradient descent with `η = 1/β` on a convex `β`-smooth `f`
over a compact convex `X`, with `x*` a minimizer of `f` on `X` and `s ≥ 1`:
`f(x_{s+1}) − f(x_s) ≤ −(1/(2β))‖g_X(x_s)‖²` and `f(x_{s+1}) − f(x*) ≤ ‖g_X(x_s)‖ · ‖x_s − x*‖`,
where `g_X(x_s) = β(x_s − x_{s+1})`. -/
theorem thm_3_7_descent_gap {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothOn X f g β)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsProjGDRun X g β x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (s : ℕ) (hs : 1 ≤ s) :
    f (x (s + 1)) - f (x s) ≤ -(1 / (2 * β)) * ‖gradMap β (x s) (x (s + 1))‖ ^ 2 ∧
      f (x (s + 1)) - f xstar ≤ ‖gradMap β (x s) (x (s + 1))‖ * ‖x s - xstar‖ := by sorry

end ConvexOptAlg.ProjectedGD
