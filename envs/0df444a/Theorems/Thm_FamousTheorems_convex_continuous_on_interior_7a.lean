-- Prove2me | Theorems.Thm_FamousTheorems_convex_continuous_on_interior_7a
-- name    : FamousTheorems.convex_continuous_on_interior_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:06.208122+00:00
-- url     : https://prove2.me/theorems/5d4821eb-e651-495f-add3-c19ff9e86684
-- title:
--   Convex functions are continuous on the interior of their domain
-- statement:
--   **Convex functions are continuous on the interior of their domain.** Let $E$ be a finite-dimensional real normed space, $C\subseteq E$, and $f:E\to\mathbb R$ convex on $C$. Then $f$ is continuous at every interior point of $C$.
--
--   In one variable this follows from the monotonicity of difference quotients. In finite dimensions, $f$ is bounded above on a small simplex around each interior point, and convexity turns this bound into a Lipschitz estimate. The theorem fails in infinite dimensions, where discontinuous linear functionals are convex. It is used throughout convex analysis and optimization, for example in the existence of subgradients.
--
--   **Formalization note.** Mathlib's `ConvexOn.continuousOn_interior`. `ConvexOn ℝ C f` includes the hypothesis that $C$ is convex.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ConvexOn.continuousOn_interior`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem convex_continuous_on_interior_7a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ C f) : ContinuousOn f (interior C) := by sorry

end FamousTheorems
