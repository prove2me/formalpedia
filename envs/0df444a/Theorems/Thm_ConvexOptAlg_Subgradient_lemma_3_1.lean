-- Prove2me | Theorems.Thm_ConvexOptAlg_Subgradient_lemma_3_1
-- name    : ConvexOptAlg.Subgradient.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:40:33.951048+00:00
-- url     : https://prove2.me/theorems/0dd1aeff-4469-4d84-8573-744ba77d6f71
-- title:
--   Lemma 3.1, p. 263 — ‖Π_X(y) − x‖² + ‖y − Π_X(y)‖² ≤ ‖y − x‖² for x ∈ X
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be convex, let $x\in\mathcal X$ and $y\in\mathbb R^n$, and let $\Pi_{\mathcal X}(y)$ be a point of $\mathcal X$ nearest to $y$ in the Euclidean norm. Then
--   $$\|\Pi_{\mathcal X}(y)-x\|^2+\|y-\Pi_{\mathcal X}(y)\|^2\le\|y-x\|^2 .$$
--
--   Projecting onto a convex set therefore never moves a point farther from any point of the set; this is the fact that lets the projected subgradient method ignore the projection step in its distance bookkeeping.
--
--   **Formalization Note** This is the second claim of Lemma 3.1. Its first claim, $(\Pi_{\mathcal X}(y)-x)^\top(\Pi_{\mathcal X}(y)-y)\le0$, is the published theorem `ConvexOptimization.projection_iff_obtuse_angle` (forward direction), which is a separate item of this mission. The projection is given as a relation (`IsMetricProjection`), so no closedness of $\mathcal X$ is needed: the statement is about any nearest point.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.1, p. 263

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol
import Definitions.Def_ConvexOptAlg_Subgradient_Defs

namespace ConvexOptAlg.Subgradient

/-- Bubeck, Lemma 3.1, p. 263, second claim: for a convex set `X`, a point `x ∈ X` and any
`y`, the projection `p = Π_X(y)` satisfies `‖p - x‖² + ‖y - p‖² ≤ ‖y - x‖²`. The projection
is given as a relation (`IsMetricProjection X y p`: `p ∈ X` is a nearest point of `X` to `y`).
The first claim `(Π_X(y) - x)ᵀ(Π_X(y) - y) ≤ 0` is the published
`ConvexOptimization.projection_iff_obtuse_angle`. -/
theorem lemma_3_1 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXconv : Convex ℝ X)
    (x y p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X)
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection X y p) :
    ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by sorry

end ConvexOptAlg.Subgradient
