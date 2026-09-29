-- Prove2me | Theorems.Thm_FamousTheorems_intersecting_secants_theorem
-- name    : FamousTheorems.intersecting_secants_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:39.926354+00:00
-- url     : https://prove2.me/theorems/085dfb09-77d2-4f06-bb73-4b30c9f8d78b
-- title:
--   The intersecting secants theorem
-- statement:
--   **The intersecting secants theorem.** Let $a,b,c,d$ be points on a common circle (or sphere), with $a\ne b$ and $c\ne d$, and let $p$ be a point such that $a,b$ lie on one ray from $p$ and $c,d$ on another, so $\angle apb=0$ and $\angle cpd=0$. Then
--   $$pa\cdot pb=pc\cdot pd.$$
--
--   This is the external case of the power of a point theorem: the product is the power of $p$ with respect to the circle. With the intersecting chords and tangent–secant theorems it forms Euclid's Propositions III.35–37.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`. `Cospherical` says that the points lie on a common sphere. An angle of $0$ at $p$ means that the two points lie on the same ray from $p$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem intersecting_secants_theorem {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {a b c d p : P} (hcos : Cospherical ({a, b, c, d} : Set P)) (hab : a ≠ b) (hcd : c ≠ d)
    (hapb : ∠ a p b = 0) (hcpd : ∠ c p d = 0) : dist a p * dist b p = dist c p * dist d p := by sorry

end FamousTheorems
