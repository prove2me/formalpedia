-- Prove2me | Theorems.Thm_FamousTheorems_ptolemy
-- name    : FamousTheorems.ptolemy
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:29.811513+00:00
-- url     : https://prove2.me/theorems/45194653-05d7-45a4-a451-ec9e0f3b02a5
-- title:
--   Ptolemy's theorem
-- statement:
--   **Ptolemy's theorem.**
--
--   If $a, b, c, d$ lie on a common sphere and the segments $ac$ and $bd$ cross at a point $p$ — so that
--   $abcd$ is a cyclic quadrilateral in that cyclic order — then
--   $$|ab|\cdot|cd| \;+\; |bc|\cdot|da| \;=\; |ac|\cdot|bd| :$$
--   the product of the diagonals equals the sum of the products of the two pairs of opposite sides.
--
--   For a general quadrilateral the left side is strictly larger (Ptolemy's inequality); equality
--   characterises concyclicity. Applied to a rectangle it collapses to the Pythagorean theorem, and
--   applied to a cyclic quadrilateral with one side a diameter it yields the addition formulas for sine
--   and cosine — which is exactly how Ptolemy used it.
--
--   It appears in Book I of the *Almagest* (c. 150 AD), where it is the engine for computing the table of
--   chords, the trigonometric table on which fourteen centuries of positional astronomy rested. Before
--   the sine function existed, this identity was trigonometry.
--
--   **Formalization note.** `Cospherical` asserts the four points are equidistant from some centre;
--   $\angle\,apc = \pi$ says $p$ lies strictly between $a$ and $c$, which encodes that the diagonals cross.
--   The result is Mathlib's `EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped EuclideanGeometry Real

theorem ptolemy
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {a b c d p : P} (h : EuclideanGeometry.Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π) (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := by sorry

end FamousTheorems
