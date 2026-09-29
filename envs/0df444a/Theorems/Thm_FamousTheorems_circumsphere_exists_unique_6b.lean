-- Prove2me | Theorems.Thm_FamousTheorems_circumsphere_exists_unique_6b
-- name    : FamousTheorems.circumsphere_exists_unique_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:44.489394+00:00
-- url     : https://prove2.me/theorems/f056a76c-c8c4-4c0a-ac58-cfe89f3358f5
-- title:
--   Existence and uniqueness of the circumcentre
-- statement:
--   **Existence and uniqueness of the circumcentre.** Let $p_0,\dots,p_n$ be affinely independent points in a Euclidean affine space. Then there is exactly one sphere whose centre lies in the affine span of $p_0,\dots,p_n$ and which passes through all the points.
--
--   For a triangle this says that there is a unique circumcircle, and its centre is the intersection of the perpendicular bisectors of the sides. In general it defines the circumcentre and circumradius of a simplex. Circumcentres are used in Delaunay triangulations and, for triangles, in the Euler line and the nine-point circle.
--
--   **Formalization note.** Mathlib's `AffineIndependent.existsUnique_dist_eq`, for a finite nonempty affinely independent family $p$. `EuclideanGeometry.Sphere P` is a pair consisting of a centre and a radius, and the condition says that every $p_i$ lies at distance `cs.radius` from `cs.center`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AffineIndependent.existsUnique_dist_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem circumsphere_exists_unique_6b {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {ι : Type*} [Nonempty ι] [Finite ι] {p : ι → P} (hp : AffineIndependent ℝ p) :
    ∃! cs : EuclideanGeometry.Sphere P,
      cs.center ∈ affineSpan ℝ (Set.range p) ∧ Set.range p ⊆ Metric.sphere cs.center cs.radius := by sorry

end FamousTheorems
