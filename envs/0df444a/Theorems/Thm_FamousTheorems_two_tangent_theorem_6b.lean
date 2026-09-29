-- Prove2me | Theorems.Thm_FamousTheorems_two_tangent_theorem_6b
-- name    : FamousTheorems.two_tangent_theorem_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:44.951576+00:00
-- url     : https://prove2.me/theorems/5835ef71-5f08-4b5b-b73d-532e5285f9a1
-- title:
--   The two tangent segments from an external point are equal (two-tangent theorem)
-- statement:
--   **The two-tangent theorem.** Let $s$ be a sphere in a Euclidean affine space, and let $\ell_1,\ell_2$ be tangent to $s$ at the points $p_1,p_2$. If a point $q$ lies on both $\ell_1$ and $\ell_2$, then
--   $$qp_1=qp_2.$$
--
--   In the plane this says that the two tangent segments from an external point to a circle are equal. It follows from Pythagoras's theorem, since $qp_i^2=qo^2-r^2$ where $o$ is the centre and $r$ the radius. It is used to prove Pitot's theorem on tangential quadrilaterals and to compute the tangent lengths of the incircle of a triangle.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem`. `s.IsTangentAt p as` says that $p$ lies on the sphere $s$ and in the affine subspace `as`, and that `as` lies in the hyperplane through $p$ orthogonal to the radius at $p$. The tangent subspaces may have any dimension.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.Sphere.IsTangentAt.dist_eq_of_mem_of_mem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem two_tangent_theorem_6b {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {s : EuclideanGeometry.Sphere P} {p₁ p₂ q : P} {as₁ as₂ : AffineSubspace ℝ P}
    (h₁ : s.IsTangentAt p₁ as₁) (h₂ : s.IsTangentAt p₂ as₂) (hq₁ : q ∈ as₁) (hq₂ : q ∈ as₂) :
    dist q p₁ = dist q p₂ := by sorry

end FamousTheorems
