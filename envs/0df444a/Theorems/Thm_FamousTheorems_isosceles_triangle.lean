-- Prove2me | Theorems.Thm_FamousTheorems_isosceles_triangle
-- name    : FamousTheorems.isosceles_triangle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:29.114622+00:00
-- url     : https://prove2.me/theorems/a910706d-6578-4def-ab32-7c44361225d8
-- title:
--   The isosceles triangle theorem (pons asinorum)
-- statement:
--   **The isosceles triangle theorem**, Euclid's *pons asinorum*.
--
--   If $d(p_1,p_2) = d(p_1,p_3)$ then the two base angles are equal:
--   $$\angle\, p_1p_2p_3 \;=\; \angle\, p_1p_3p_2 .$$
--
--   Equal sides subtend equal angles. It is Euclid I.5, the first proposition of the *Elements* that
--   requires any real argument, and the point at which readers traditionally gave up — hence "the bridge
--   of asses". Euclid's proof extends the equal sides and compares two overlapping triangles; Pappus gave
--   the slicker argument of matching the triangle with its own mirror image, which is the proof that
--   generalizes to the abstract setting here.
--
--   Together with its converse (equal angles force equal sides) it is what makes "isosceles" a meaningful
--   notion at all, and it is the first step in almost every classical construction — bisecting an angle,
--   erecting a perpendicular, inscribing a regular polygon.
--
--   **Formalization note.** `∠ p₁ p₂ p₃` is the unoriented angle at the vertex $p_2$, so the two angles
--   compared are those at the base vertices $p_2$ and $p_3$. The result is Mathlib's
--   `EuclideanGeometry.angle_eq_angle_of_dist_eq`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped EuclideanGeometry Real

theorem isosceles_triangle
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (h : dist p₁ p₂ = dist p₁ p₃) : ∠ p₁ p₂ p₃ = ∠ p₁ p₃ p₂ := by sorry

end FamousTheorems
