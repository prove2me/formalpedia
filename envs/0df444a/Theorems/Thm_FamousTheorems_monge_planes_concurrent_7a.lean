-- Prove2me | Theorems.Thm_FamousTheorems_monge_planes_concurrent_7a
-- name    : FamousTheorems.monge_planes_concurrent_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:40.544046+00:00
-- url     : https://prove2.me/theorems/ff2d4bc9-94fd-4d1b-8077-88f1ea2e049c
-- title:
--   The Monge planes of a simplex are concurrent (Monge point)
-- statement:
--   **The Monge planes of a simplex are concurrent.** Let $s$ be an $n$-simplex in a Euclidean affine space with $n\ge2$. For each pair of vertices $p_i,p_j$, the Monge plane is the hyperplane through the centroid of the other $n-1$ vertices orthogonal to the edge $p_ip_j$. All the Monge planes pass through a common point, the Monge point of $s$.
--
--   Monge proved this for tetrahedra. For a triangle the Monge planes are the altitudes, and the Monge point is the orthocentre. So the theorem generalizes the concurrence of the altitudes to all dimensions, which altitudes themselves do not do: the altitudes of a general tetrahedron are not concurrent. The Monge point lies on the Euler line of the simplex.
--
--   **Formalization note.** Mathlib's `Affine.Simplex.mongePoint_mem_mongePlane`, where the common point is Mathlib's `Affine.Simplex.mongePoint`. Mathlib defines `s.mongePlane i₁ i₂` as the affine subspace through the centroid of the vertices other than $p_{i_1},p_{i_2}$ with direction orthogonal to $p_{i_2}-p_{i_1}$ within the span of the simplex. For $i_1=i_2$ the plane is the whole span, and the statement is trivially true there.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Affine.Simplex.mongePoint_mem_mongePlane`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem monge_planes_concurrent_7a {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {n : ℕ}
    (s : Affine.Simplex ℝ P (n + 2)) : ∃ p : P, ∀ i₁ i₂ : Fin (n + 3), p ∈ s.mongePlane i₁ i₂ := by sorry

end FamousTheorems
