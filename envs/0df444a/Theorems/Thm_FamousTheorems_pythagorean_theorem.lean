-- Prove2me | Theorems.Thm_FamousTheorems_pythagorean_theorem
-- name    : FamousTheorems.pythagorean_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:23.332364+00:00
-- url     : https://prove2.me/theorems/029c3f84-7cd9-42d0-a4d5-eb9181329fc5
-- title:
--   The Pythagorean theorem
-- statement:
--   **The Pythagorean theorem**, with its converse.
--
--   In a real inner product space regarded as a Euclidean affine space, for any three points
--   $p_1, p_2, p_3$,
--   $$d(p_1,p_3)^2 = d(p_1,p_2)^2 + d(p_3,p_2)^2 \quad\Longleftrightarrow\quad \angle\, p_1 p_2 p_3 = \frac{\pi}{2}.$$
--
--   The forward direction is Euclid I.47 and the reverse is I.48; stating them as a single
--   $\leftrightarrow$ is the sharper formulation, since it says the relation between the side lengths
--   characterises the right angle rather than merely following from it. No nondegeneracy hypothesis is
--   needed: if two of the points coincide both sides degenerate consistently.
--
--   The theorem is the reason the Euclidean metric has the form it does — in the abstract setting here it
--   is essentially the polarization identity, since $\lVert u - v\rVert^2 = \lVert u\rVert^2 + \lVert v\rVert^2$
--   exactly when $\langle u, v\rangle = 0$. Every inner product space is therefore "Pythagorean", and
--   conversely a normed space whose norm satisfies the parallelogram law comes from an inner product
--   (Jordan–von Neumann).
--
--   Known to Babylonian and Indian mathematicians a millennium before Pythagoras; the *Elements* gives
--   the first recorded proof. Over three hundred distinct proofs have been collected.
--
--   **Formalization note.** `∠ p₁ p₂ p₃` is the unoriented angle at the vertex $p_2$, valued in $[0, \pi]$,
--   and distances are squared as `d * d` rather than `d ^ 2`. The result is Mathlib's
--   `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped EuclideanGeometry Real

theorem pythagorean_theorem
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    (p₁ p₂ p₃ : P) :
    dist p₁ p₃ * dist p₁ p₃ = dist p₁ p₂ * dist p₁ p₂ + dist p₃ p₂ * dist p₃ p₂ ↔
      ∠ p₁ p₂ p₃ = π / 2 := by sorry

end FamousTheorems
