-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_thm_3_7_recursion
-- name    : ConvexOptAlg.ProjectedGD.thm_3_7_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:13:29.357999+00:00
-- url     : https://prove2.me/theorems/ed88b456-1ed7-4e77-90d9-af5b43fb6a00
-- title:
--   Proof of Theorem 3.7, p. 271 — δ_{s+1} ≤ δ_s − δ_{s+1}²/(2β‖x₁ − x*‖²), multiplied out
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, $f$ convex and $\beta$-smooth on $\mathcal X$ with $\beta>0$, and $x^*\in\mathcal X$ a minimizer of $f$ on $\mathcal X$. Let $(x_t)_{t\ge1}$ be a run of projected gradient descent with step size $\eta=1/\beta$, and put $\delta_s=f(x_s)-f(x^*)$. Then for every $s\ge1$,
--   $$\delta_{s+1}^2\le2\beta\|x_1-x^*\|^2\,(\delta_s-\delta_{s+1}) .$$
--
--   When $x_1\neq x^*$ this is the book's recursion
--   $$\delta_{s+1}\le\delta_s-\frac1{2\beta\|x_1-x^*\|^2}\,\delta_{s+1}^2 ,$$
--   which, by an induction on $s$, gives the rate of Theorem 3.7.
--
--   **Formalization Note** The recursion is stated multiplied by $2\beta\|x_1-x^*\|^2$, so that no division by $\|x_1-x^*\|^2$ (which is $0$ when $x_1=x^*$) occurs; for $x_1\ne x^*$ the two forms are equivalent. The existence of a minimizer is the book's standing assumption; $\beta>0$ is implicit in the step $1/\beta$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.7, p. 271 (third display)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_ProjectedGD_Defs

open scoped InnerProductSpace
open OnlineConvexOpt.FirstOrder

namespace ConvexOptAlg.ProjectedGD

/-- The recursion in the proof of Theorem 3.7 (Bubeck, arXiv:1405.4980v2, p. 271), multiplied out:
with `δ_s = f(x_s) − f(x*)`, `δ_{s+1} ≤ δ_s − (1/(2β‖x₁ − x*‖²)) δ_{s+1}²` is stated as
`δ_{s+1}² ≤ 2β‖x₁ − x*‖² (δ_s − δ_{s+1})`, for every `s ≥ 1`, so that no division by
`‖x₁ − x*‖²` (which may be `0`) occurs. -/
theorem thm_3_7_recursion {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsBetaSmoothOn X f g β)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsProjGDRun X g β x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (s : ℕ) (hs : 1 ≤ s) :
    (f (x (s + 1)) - f xstar) ^ 2 ≤
      2 * β * ‖x 1 - xstar‖ ^ 2 * ((f (x s) - f xstar) - (f (x (s + 1)) - f xstar)) := by sorry

end ConvexOptAlg.ProjectedGD
