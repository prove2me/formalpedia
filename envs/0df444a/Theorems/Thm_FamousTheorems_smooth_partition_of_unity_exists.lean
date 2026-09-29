-- Prove2me | Theorems.Thm_FamousTheorems_smooth_partition_of_unity_exists
-- name    : FamousTheorems.smooth_partition_of_unity_exists
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:33.744426+00:00
-- url     : https://prove2.me/theorems/a9bae1a8-a0aa-46ff-af25-a80499dbd77f
-- title:
--   Existence of smooth partitions of unity
-- statement:
--   **Existence of smooth partitions of unity.** Let $M$ be a Hausdorff, $\sigma$-compact smooth manifold (possibly with boundary or corners) modelled on a finite-dimensional real space, $s\subseteq M$ closed, and $(U_i)$ an open cover of $s$. Then there is a smooth partition of unity on $s$ subordinate to $(U_i)$: smooth functions $f_i:M\to[0,1]$ with locally finite supports, $\operatorname{supp}f_i\subseteq U_i$, and $\sum_i f_i=1$ on $s$.
--
--   Partitions of unity are the standard device for passing from local to global constructions on manifolds: building Riemannian metrics, integrating differential forms, and proving the Whitney embedding theorem.
--
--   **Formalization note.** Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`. Smoothness is $C^\infty$ (`IsManifold I ∞ M`, with `∞` from `open scoped ContDiff`). `f.IsSubordinate U` means the closure of the support of each `f i` lies in `U i`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SmoothPartitionOfUnity.exists_isSubordinate`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped ContDiff

theorem smooth_partition_of_unity_exists {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by sorry

end FamousTheorems
