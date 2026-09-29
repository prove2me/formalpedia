-- Prove2me | Theorems.Thm_FamousTheorems_isosceles_triangle_converse_7a
-- name    : FamousTheorems.isosceles_triangle_converse_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:40.66597+00:00
-- url     : https://prove2.me/theorems/de99edcf-8a67-4ad8-a50b-49bfc85ab910
-- title:
--   Converse of the isosceles triangle theorem
-- statement:
--   **Converse of the isosceles triangle theorem.** Let $p_1,p_2,p_3$ be points in a Euclidean affine space with $\angle p_1p_2p_3=\angle p_1p_3p_2$. If the angle at $p_1$ is not $\pi$, then $|p_1p_2|=|p_1p_3|$.
--
--   This is the converse of Euclid's *Elements* I.5 and appears as Proposition I.6: a triangle with two equal angles has the opposite sides equal. The hypothesis $\angle p_2p_1p_3\ne\pi$ excludes a degenerate configuration in which $p_1$ lies strictly between $p_2$ and $p_3$, where both base angles are $0$ but the sides may differ.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi`. `∠ a b c` is the unoriented angle at $b$, with values in $[0,\pi]$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem isosceles_triangle_converse_7a {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {p₁ p₂ p₃ : P}
    (h : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂) (hpi : ∠ p₂ p₁ p₃ ≠ Real.pi) : dist p₁ p₂ = dist p₁ p₃ := by sorry

end FamousTheorems
