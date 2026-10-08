-- Prove2me | Theorems.Thm_ConvexOptAlg_Subgradient_theorem_3_2
-- name    : ConvexOptAlg.Subgradient.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:40:59.322992+00:00
-- url     : https://prove2.me/theorems/0fc47197-f60d-4b2f-ac9d-ed0ad76f289e
-- title:
--   Theorem 3.2, pp. 264–265 — projected subgradient descent with η = R/(L√t) satisfies f((1/t)Σ x_s) − f(x*) ≤ RL/√t
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex and $f:\mathcal X\to\mathbb R$ convex, with a minimizer $x^*\in\mathcal X$. Let $R>0$ and $L>0$, and fix a horizon $t\ge1$. Let $(x_s),(g_s)$ be a run of projected subgradient descent
--   $$y_{s+1}=x_s-\eta g_s,\quad g_s\in\partial f(x_s),\qquad x_{s+1}=\Pi_{\mathcal X}(y_{s+1}),\qquad s=1,\dots,t,$$
--   with the constant step $\eta=R/(L\sqrt t)$, such that $\mathcal X$ is contained in the Euclidean ball of radius $R$ centred at $x_1\in\mathcal X$ and $\|g_s\|\le L$ for $1\le s\le t$. Then
--   $$f\Big(\frac1t\sum_{s=1}^{t}x_s\Big)-f(x^*)\le\frac{RL}{\sqrt t}.$$
--
--   This is the dimension-free $O(1/\sqrt t)$ rate of the projected subgradient method for Lipschitz convex functions; Section 3.5 of the book shows it cannot be improved for black-box first-order methods.
--
--   **Formalization Note** $\partial f(x)$ is the set of subgradients relative to $\mathcal X$ (Definition 1.2), and any choice of subgradient is allowed at each step. Compactness and convexity of $\mathcal X$, convexity of $f$ and the existence of $x^*$ are the standing assumptions of Chapter 3 and of the book. $R>0$ and $L>0$ make the step and the bound well defined (Lean's $a/0=0$ would otherwise give a junk step). The page assumes $\|g\|\le L$ for every subgradient at every point of $\mathcal X$ (with $\partial f(x)\neq\emptyset$); here the bound is assumed only for the subgradients the run uses, a weaker hypothesis and hence a stronger statement. Taken literally with relative subgradients, the page's bound fails at every boundary point of a nonempty compact $\mathcal X$ in $\mathbb R^n$, $n\ge1$, so the run-wise bound is also what keeps the statement non-vacuous. The run is required only for the steps $1,\dots,t$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 3.2, pp. 264–265 (with the assumptions of the Ch. 3 preamble, pp. 262–263, and §3.1, pp. 263–264)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs

namespace ConvexOptAlg.Subgradient

/-- Bubeck, Theorem 3.2, pp. 264–265: under the assumptions of Chapter 3 and §3.1 (`X` compact
convex, `f` convex on `X`, `X` inside the ball of radius `R > 0` centred at `x₁`, subgradients
bounded by `L > 0`, `x*` a minimizer of `f` on `X`), for every horizon `t ≥ 1`, projected
subgradient descent run for `t` steps with the constant step `η = R/(L√t)` satisfies
`f((1/t) ∑_{s=1}^t x_s) - f(x*) ≤ RL/√t`. The bound `‖g_s‖ ≤ L` is assumed only for the
subgradients the run uses (a weaker hypothesis than the page's). -/
theorem theorem_3_2 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXcpt : IsCompact X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ X f)
    (R L : ℝ) (hR : 0 < R) (hLpos : 0 < L) (t : ℕ) (ht : 1 ≤ t)
    (x g : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : IsProjSubgradRun X f (fun _ => R / (L * Real.sqrt t)) x g t)
    (hball : X ⊆ Metric.closedBall (x 1) R)
    (hL : ∀ s, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, x s) - f xstar ≤ R * L / Real.sqrt t := by sorry

end ConvexOptAlg.Subgradient
