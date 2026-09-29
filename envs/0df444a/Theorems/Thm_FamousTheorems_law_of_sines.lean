-- Prove2me | Theorems.Thm_FamousTheorems_law_of_sines
-- name    : FamousTheorems.law_of_sines
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:12.411771+00:00
-- url     : https://prove2.me/theorems/4eb6bdce-fcef-410e-bd8a-b996cb6611fa
-- title:
--   The law of sines
-- statement:
--   **The law of sines.** In any triangle $p_1p_2p_3$ in a real inner product space (or Euclidean affine space),
--   $$\sin\angle p_2\cdot|p_2p_3|=\sin\angle p_1\cdot|p_3p_1|,$$
--   where $\angle p_i$ is the angle at vertex $p_i$. For a nondegenerate triangle this is the familiar $\dfrac{a}{\sin A}=\dfrac{b}{\sin B}$.
--
--   Together with the law of cosines, the law of sines is the basic tool for solving triangles. It is used in surveying, navigation and astronomy, and it is equivalent to the fact that all three ratios equal the diameter of the circumcircle.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. `EuclideanGeometry.angle p₁ p₂ p₃` is the unoriented angle at `p₂`. The statement is in product form, so it also holds for degenerate triangles, where the quotient form would divide by zero.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.sin_angle_mul_dist_eq_sin_angle_mul_dist`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem law_of_sines {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) :
    Real.sin (EuclideanGeometry.angle p₁ p₂ p₃) * dist p₂ p₃ =
      Real.sin (EuclideanGeometry.angle p₃ p₁ p₂) * dist p₃ p₁ := by sorry

end FamousTheorems
