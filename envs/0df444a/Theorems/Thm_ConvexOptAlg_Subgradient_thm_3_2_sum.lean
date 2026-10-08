-- Prove2me | Theorems.Thm_ConvexOptAlg_Subgradient_thm_3_2_sum
-- name    : ConvexOptAlg.Subgradient.thm_3_2_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:40:59.765108+00:00
-- url     : https://prove2.me/theorems/c635efaf-7130-4c44-9316-6ae1d1ded25f
-- title:
--   §3.1, proof of Theorem 3.2, p. 265 — Σ_{s=1}^t (f(x_s) − f(x*)) ≤ R²/(2η) + ηL²t/2
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, $f$ convex on $\mathcal X$, and $x^*\in\mathcal X$ a minimizer of $f$ on $\mathcal X$. Let $\eta>0$, $R>0$, $L\in\mathbb R$ and $t\in\mathbb N$, and let $(x_s),(g_s)$ be a run of projected subgradient descent with constant step $\eta$ for the steps $1,\dots,t$, such that $\mathcal X$ is contained in the closed Euclidean ball of radius $R$ centred at $x_1$ and $\|g_s\|\le L$ for $1\le s\le t$. Then
--   $$\sum_{s=1}^{t}\big(f(x_s)-f(x^*)\big)\le\frac{R^2}{2\eta}+\frac{\eta L^2 t}{2}.$$
--
--   Dividing by $t$ and choosing $\eta$ to balance the two terms gives Theorem 3.2.
--
--   **Formalization Note** Compactness of $\mathcal X$, convexity of $f$ and the existence of the minimizer $x^*$ are the standing assumptions of Chapter 3 and of the book. The page assumes $\|g\|\le L$ for every subgradient at every point of $\mathcal X$; here the bound is assumed only for the subgradients $g_1,\dots,g_t$ used by the run, a weaker hypothesis (so a stronger statement). With subgradients taken relative to $\mathcal X$, the page's form of the bound could never hold at a boundary point of a compact set (the relative subdifferential there contains every outward normal), so the run-wise bound is also what keeps the statement non-vacuous.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.1, proof of Theorem 3.2, p. 265, second display

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs

namespace ConvexOptAlg.Subgradient

/-- Bubeck, proof of Theorem 3.2, p. 265, second display: under the assumptions of Chapter 3
and §3.1 (`X` compact convex, `f` convex on `X`, `X` inside the ball of radius `R` centred at
`x₁`, subgradients bounded by `L`, `x*` a minimizer of `f` on `X`), a run of projected
subgradient descent with constant step `η > 0` satisfies
`∑_{s=1}^t (f(x_s) - f(x*)) ≤ R²/(2η) + ηL²t/2`. The bound `‖g_s‖ ≤ L` is assumed only for the
subgradients the run uses. -/
theorem thm_3_2_sum {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcpt : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ X f)
    (R L η : ℝ) (hR : 0 < R) (hη : 0 < η) (t : ℕ)
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsProjSubgradRun X f (fun _ => η) x g t)
    (hball : X ⊆ Metric.closedBall (x 1) R)
    (hL : ∀ s, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f xstar) ≤
      R ^ 2 / (2 * η) + η * L ^ 2 * (t : ℝ) / 2 := by sorry

end ConvexOptAlg.Subgradient
