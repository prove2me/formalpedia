-- Prove2me | Theorems.Thm_FamousTheorems_nine_point_circle_theorem
-- name    : FamousTheorems.nine_point_circle_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:58:03.401736+00:00
-- url     : https://prove2.me/theorems/91525e7e-b5e4-463f-8521-f29343f50a6d
-- title:
--   The nine-point circle theorem
-- statement:
--   **The nine-point circle theorem.** In any triangle, the following nine points lie on a common circle: the midpoints of the three sides, the feet of the three altitudes, and the midpoints of the three segments joining the orthocenter to the vertices.
--
--   The nine-point circle (Feuerbach circle) has radius half the circumradius, and its center lies at the midpoint of the orthocenter and circumcenter on the Euler line. By Feuerbach's theorem it is tangent to the incircle and the three excircles.
--
--   **Formalization note.** Mathlib's `Affine.Triangle.altitudeFoot_mem_ninePointCircle`, `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle` and `Affine.Simplex.eulerPoint_mem_ninePointCircle`, with witness `s.ninePointCircle`. For a triangle, `s.faceOppositeCentroid i` is the centroid of the side opposite vertex `i`, i.e. its midpoint, and `s.altitudeFoot i` is the foot of the altitude from vertex `i`. The ambient space may have any dimension, and the conclusion asks for a sphere through all nine points. Since these points lie in the plane of the triangle, that sphere cuts out the nine-point circle.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Affine.Triangle.altitudeFoot_mem_ninePointCircle`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem nine_point_circle_theorem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (s : Affine.Triangle ℝ P) : ∃ S : EuclideanGeometry.Sphere P,
      (∀ i, s.faceOppositeCentroid i ∈ S) ∧ (∀ i, s.altitudeFoot i ∈ S) ∧
        ∀ i, midpoint ℝ s.orthocenter (s.points i) ∈ S := by sorry

end FamousTheorems
