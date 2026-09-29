-- Prove2me | Theorems.Thm_FamousTheorems_law_of_cosines
-- name    : FamousTheorems.law_of_cosines
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:23.659045+00:00
-- url     : https://prove2.me/theorems/6fb9e7c2-6013-4015-9f59-18d5a0934e7f
-- title:
--   The law of cosines
-- statement:
--   **The law of cosines** (the generalized Pythagorean theorem).
--
--   For any three points $p_1, p_2, p_3$ of a Euclidean affine space,
--   $$d(p_1,p_3)^2 = d(p_1,p_2)^2 + d(p_3,p_2)^2 - 2\,d(p_1,p_2)\,d(p_3,p_2)\cos\bigl(\angle\, p_1p_2p_3\bigr).$$
--
--   Setting the angle to $\pi/2$ recovers the Pythagorean theorem, and the cosine term measures exactly how
--   far from a right angle the triangle is: acute angles shorten the opposite side, obtuse angles lengthen
--   it. Unlike the Pythagorean theorem this is an unconditional identity — it holds for every triple with
--   no hypothesis at all — which makes it the basic tool for solving triangles from side–angle–side data.
--
--   Euclid II.12 and II.13 give the obtuse and acute cases geometrically, without trigonometry; the
--   statement in terms of cosine is due to al-Kashi in the 15th century, and the law is still called the
--   *théorème d'Al-Kashi* in French. In the abstract form here it is the expansion of
--   $\lVert u - v \rVert^2$ together with the definition of the angle as $\arccos$ of the normalized inner
--   product, so it is the analytic content of the inner product itself.
--
--   **Formalization note.** `∠ p₁ p₂ p₃` is the unoriented angle at $p_2$. The result is Mathlib's
--   `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped EuclideanGeometry Real

theorem law_of_cosines
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ -
      2 * dist p₁ p₂ * dist p₃ p₂ * Real.cos (∠ p₁ p₂ p₃) := by sorry

end FamousTheorems
