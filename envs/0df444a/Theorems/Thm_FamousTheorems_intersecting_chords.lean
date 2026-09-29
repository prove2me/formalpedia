-- Prove2me | Theorems.Thm_FamousTheorems_intersecting_chords
-- name    : FamousTheorems.intersecting_chords
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:34.074289+00:00
-- url     : https://prove2.me/theorems/71649a82-c9b4-48f0-9498-af7818b07e68
-- title:
--   Product of the segments of chords
-- statement:
--   **The intersecting chords theorem.**
--
--   If $a, b, c, d$ lie on a common sphere and the chords $ab$ and $cd$ both pass through a point $p$,
--   then
--   $$|ap|\cdot|bp| \;=\; |cp|\cdot|dp| .$$
--
--   The common value depends only on $p$ and the sphere, not on the chord chosen: it is $r^2 - d(O,p)^2$
--   where $O$ is the centre. That quantity is the *power of the point* $p$, and this theorem is the
--   statement that the power is well defined — which is why every chord through $p$ is split in the same
--   proportion. The external version, with $p$ outside the circle, gives the tangent–secant relation, and
--   the locus of points of equal power with respect to two circles is their radical axis.
--
--   Euclid proves it as III.35, with III.36 and III.37 for the external cases. Steiner's systematic use of
--   the power of a point in the 1820s turned it from a proposition about circles into the organising idea
--   of inversive geometry.
--
--   **Formalization note.** $\angle\,apb = \pi$ says $p$ lies strictly between $a$ and $b$, i.e. $p$ is
--   interior to the chord. The result is Mathlib's
--   `EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped EuclideanGeometry Real

theorem intersecting_chords
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c d p : P} (h : EuclideanGeometry.Cospherical ({a, b, c, d} : Set P))
    (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) :
    dist a p * dist b p = dist c p * dist d p := by sorry

end FamousTheorems
