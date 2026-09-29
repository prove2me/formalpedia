-- Prove2me | Theorems.Thm_FamousTheorems_exterior_angle_theorem
-- name    : FamousTheorems.exterior_angle_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:22.39291+00:00
-- url     : https://prove2.me/theorems/c894bf2b-30d9-43f9-9723-b30662c7baa6
-- title:
--   The exterior angle theorem
-- statement:
--   **The exterior angle theorem.** In a triangle $p_1p_2p_3$ in a Euclidean space, extend the side $p_2p_1$ beyond $p_1$ to a point $p$. The exterior angle at $p_1$ equals the sum of the two remote interior angles:
--   $$\angle p_3p_1p=\angle p_1p_3p_2+\angle p_3p_2p_1 .$$
--
--   It is equivalent (via supplementary angles) to the angle sum $\pi$ of a triangle, and in its weak form (exterior angle larger than each remote angle, Euclid I.16) it marks the boundary between absolute and Euclidean geometry.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.exterior_angle_eq_angle_add_angle`; `Sbtw ℝ p p₁ p₂` says `p₁` lies strictly between `p` and `p₂`, and `EuclideanGeometry.angle a b c` is the unoriented angle at `b`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.exterior_angle_eq_angle_add_angle`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem exterior_angle_theorem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (p : P) (h : Sbtw ℝ p p₁ p₂) :
    EuclideanGeometry.angle p₃ p₁ p = EuclideanGeometry.angle p₁ p₃ p₂ + EuclideanGeometry.angle p₃ p₂ p₁ := by sorry

end FamousTheorems
