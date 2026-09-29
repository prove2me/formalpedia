-- Prove2me | Theorems.Thm_FamousTheorems_angle_triangle_inequality
-- name    : FamousTheorems.angle_triangle_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:49.604124+00:00
-- url     : https://prove2.me/theorems/83468e82-e798-4994-ba66-c3fb69c55c19
-- title:
--   The triangle inequality for angles
-- statement:
--   **The triangle inequality for angles.** For all points $p,p_1,p_2,p_3$ in a Euclidean affine space,
--   $$\angle p_1pp_3\le\angle p_1pp_2+\angle p_2pp_3.$$
--
--   The inequality says that the angle between vectors is a metric on the unit sphere, the great-circle distance. It is essentially Euclid's Proposition XI.20: of the three plane angles forming a solid angle, any two together exceed the third.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.angle_le_angle_add_angle`. `∠ a b c` is the unoriented angle at $b$, valued in $[0,\pi]$. The statement holds for all points, including degenerate ones, with Mathlib's convention that the angle involving a zero vector is $\pi/2$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.angle_le_angle_add_angle`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem angle_triangle_inequality {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p p₁ p₂ p₃ : P) : ∠ p₁ p p₃ ≤ ∠ p₁ p p₂ + ∠ p₂ p p₃ := by sorry

end FamousTheorems
