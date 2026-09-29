-- Prove2me | Theorems.Thm_FamousTheorems_vertical_angles_theorem
-- name    : FamousTheorems.vertical_angles_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:36.233255+00:00
-- url     : https://prove2.me/theorems/bab65099-a07d-4d6a-9f3b-780689bcaab6
-- title:
--   The vertical angles theorem
-- statement:
--   **The vertical angles theorem.** Let two lines meet at a point $p_5$, with $p_1,p_3$ on one line and $p_2,p_4$ on the other, on opposite sides of $p_5$: $\angle p_1p_5p_3=\pi$ and $\angle p_2p_5p_4=\pi$. Then the vertical angles are equal:
--   $$\angle p_1p_5p_2=\angle p_3p_5p_4.$$
--
--   This is Proposition I.15 of Euclid's Elements, one of the first theorems of plane geometry.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi`, stated in any real inner product space. `∠ a b c` is the unoriented angle at $b$, valued in $[0,\pi]$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem vertical_angles_theorem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ p₄ p₅ : P} (h₁ : ∠ p₁ p₅ p₃ = Real.pi) (h₂ : ∠ p₂ p₅ p₄ = Real.pi) : ∠ p₁ p₅ p₂ = ∠ p₃ p₅ p₄ := by sorry

end FamousTheorems
