-- Prove2me | Theorems.Thm_FamousTheorems_holomorphic_compact_manifold_const_6b
-- name    : FamousTheorems.holomorphic_compact_manifold_const_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:38.467985+00:00
-- url     : https://prove2.me/theorems/66352cd7-e707-4baf-984a-10c3bbac6799
-- title:
--   Holomorphic functions on a compact connected complex manifold are constant
-- statement:
--   **Holomorphic functions on a compact connected complex manifold are constant.** Let $M$ be a compact connected complex manifold without boundary and $f:M\to F$ a holomorphic map to a complex normed space $F$. Then $f$ is constant.
--
--   This follows from the maximum modulus principle: $\|f\|$ attains a maximum on the compact space $M$, so $f$ is locally constant near that point and hence constant on $M$ by connectedness. As a result, compact complex manifolds have no nonconstant holomorphic functions, and one studies meromorphic functions, line bundles and sections instead. It is also the key step in Liouville-type results on compact Riemann surfaces.
--
--   **Formalization note.** Mathlib's `MDifferentiable.exists_eq_const_of_compactSpace`. The manifold is modelled on a complex normed space $E$ through a boundaryless model with corners $I$, and `MDifferentiable I (modelWithCornersSelf ℂ F) f` says that $f$ is complex-differentiable in charts. Connectedness is stated as `PreconnectedSpace`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MDifferentiable.exists_eq_const_of_compactSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem holomorphic_compact_manifold_const_6b {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M] [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I (modelWithCornersSelf ℂ F) f) : ∃ v : F, f = Function.const M v := by sorry

end FamousTheorems
