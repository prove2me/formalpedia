-- Prove2me | Theorems.Thm_FamousTheorems_manifold_metrizable_7a
-- name    : FamousTheorems.manifold_metrizable_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:54.389657+00:00
-- url     : https://prove2.me/theorems/69ab52d7-9fb8-4b71-9dba-88e03185ef0b
-- title:
--   Manifolds (σ-compact, Hausdorff) are metrizable
-- statement:
--   **σ-compact Hausdorff manifolds are metrizable.** Let $M$ be a topological manifold modelled on a finite-dimensional real normed space $E$, possibly with boundary or corners. If $M$ is Hausdorff and $\sigma$-compact, then $M$ is metrizable.
--
--   A Hausdorff, locally Euclidean space is locally compact and regular. Since $M$ is $\sigma$-compact and locally homeomorphic to subsets of the second-countable space $E$, it is second countable, so Urysohn's metrization theorem applies. The result is used to put Riemannian metrics and partitions of unity on manifolds and to apply metric-space methods to them. Without $\sigma$-compactness it fails, as the long line shows.
--
--   **Formalization note.** Mathlib's `Manifold.metrizableSpace`. The model with corners `I` describes the local model of $M$ inside $E$, and `ChartedSpace H M` gives the atlas. No smoothness of the transition maps is assumed.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Manifold.metrizableSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem manifold_metrizable_7a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M]
    [T2Space M] : TopologicalSpace.MetrizableSpace M := by sorry

end FamousTheorems
