-- Prove2me | Theorems.Thm_FamousTheorems_angle_sum_triangle
-- name    : FamousTheorems.angle_sum_triangle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:42:24.165793+00:00
-- url     : https://prove2.me/theorems/df907ea8-5b61-458a-b20e-c03c37cdc37d
-- title:
--   Sum of the angles of a triangle
-- statement:
--   **The angle sum of a triangle.**
--
--   For points $p_1, p_2, p_3$ in a Euclidean affine space with $p_2 \neq p_1$,
--   $$\angle\, p_1p_2p_3 \;+\; \angle\, p_2p_3p_1 \;+\; \angle\, p_3p_1p_2 \;=\; \pi .$$
--
--   Only one nondegeneracy hypothesis is needed, not three: the identity survives the collinear and
--   coincident cases so long as the single pair $p_1, p_2$ is distinct, since the unoriented angle at a
--   repeated point is $\pi/2$ by convention and the remaining two angles then compensate.
--
--   This is Euclid I.32, and it is the proposition that is equivalent to the parallel postulate — the
--   angle sum is less than $\pi$ in hyperbolic geometry and greater in spherical geometry, with the
--   deficit or excess proportional to the area. Legendre's repeated failed attempts to derive it from the
--   other axioms, and Gauss's, Bolyai's and Lobachevsky's recognition that it cannot be so derived, are
--   the origin of non-Euclidean geometry. That it holds here without further assumption is a property of
--   inner product spaces.
--
--   **Formalization note.** `∠` is the unoriented angle, valued in $[0, \pi]$. The result is Mathlib's
--   `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped EuclideanGeometry Real

theorem angle_sum_triangle
    {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π := by sorry

end FamousTheorems
