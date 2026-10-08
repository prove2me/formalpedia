-- Prove2me | Theorems.Thm_ConvexOptAlg_ProjectedGD_lemma_3_1_pythagoras
-- name    : ConvexOptAlg.ProjectedGD.lemma_3_1_pythagoras
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:52:45.544643+00:00
-- url     : https://prove2.me/theorems/9dc2cc79-9720-4705-b5fb-a30bc74804d7
-- title:
--   Lemma 3.1 (second claim), p. 263 — ‖Π_X(y) − x‖² + ‖y − Π_X(y)‖² ≤ ‖y − x‖² for x ∈ X
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^n$ be compact and convex, let $x\in\mathcal X$ and $y\in\mathbb R^n$, and let $\Pi_{\mathcal X}(y)$ be the Euclidean projection of $y$ onto $\mathcal X$ (a point of $\mathcal X$ nearest to $y$). Then
--   $$\|\Pi_{\mathcal X}(y)-x\|^2+\|y-\Pi_{\mathcal X}(y)\|^2\le\|y-x\|^2 .$$
--
--   This is the second claim of Lemma 3.1: projecting onto a convex set does not increase the distance to any point of the set, with the squared distance gained by the projection as a bonus. It is the inequality that controls the projection step in the analysis of projected (sub)gradient methods.
--
--   **Formalization Note** The projection is any point `p` with `IsMetricProjection X y p`. Compactness and convexity of $\mathcal X$ are the standing assumption of Chapter 3 (p. 262). The first claim of Lemma 3.1, $(\Pi_{\mathcal X}(y)-x)^\top(\Pi_{\mathcal X}(y)-y)\le0$, is the published theorem `ConvexOptimization.projection_iff_obtuse_angle`, referenced by the mission.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.1, p. 263

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

namespace ConvexOptAlg.ProjectedGD

/-- Second claim of Lemma 3.1 (Bubeck, arXiv:1405.4980v2, p. 263): for `X` compact and convex
(the standing assumption of Chapter 3, p. 262), `x ∈ X` and any `y`, the projection
`Π_X(y)` (any point `p` with `IsMetricProjection X y p`) satisfies
`‖Π_X(y) − x‖² + ‖y − Π_X(y)‖² ≤ ‖y − x‖²`. -/
theorem lemma_3_1_pythagoras {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x y p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hp : IsMetricProjection X y p) :
    ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by sorry

end ConvexOptAlg.ProjectedGD
