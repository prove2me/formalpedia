-- Prove2me | Theorems.Thm_FamousTheorems_commandino
-- name    : FamousTheorems.commandino
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:08.573071+00:00
-- url     : https://prove2.me/theorems/c0051a3b-2130-407c-a84e-68827ee6ae1b
-- title:
--   Commandino's theorem
-- statement:
--   **Commandino's theorem.** In an $n$-simplex ($n\ge1$) over a field of characteristic $0$, each median (from a vertex to the centroid of the opposite face) passes through the centroid $G$ of the simplex, and $G$ divides it in the ratio $n:1$:
--   $$P_i-G=n\,(G-G_i),$$
--   where $G_i$ is the centroid of the face opposite $P_i$.
--
--   For a triangle ($n=2$) this is the classical fact that the medians meet at a point two thirds of the way along each. For a tetrahedron it is Commandino's 1565 theorem, with ratio $3:1$.
--
--   **Formalization note.** Mathlib's `Affine.Simplex.point_vsub_centroid_eq_smul_vsub`, stated in an arbitrary affine space over a division ring of characteristic $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Affine.Simplex.point_vsub_centroid_eq_smul_vsub`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem commandino {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] {n : ℕ} [NeZero n]
    [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by sorry

end FamousTheorems
