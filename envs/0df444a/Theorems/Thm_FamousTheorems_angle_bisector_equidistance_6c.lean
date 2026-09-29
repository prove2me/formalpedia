-- Prove2me | Theorems.Thm_FamousTheorems_angle_bisector_equidistance_6c
-- name    : FamousTheorems.angle_bisector_equidistance_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:27.497256+00:00
-- url     : https://prove2.me/theorems/5b8cc7ec-1531-4bec-986e-f20bca14ea9c
-- title:
--   The angle bisector theorem: equidistance from the sides characterises the bisector
-- statement:
--   **Equidistance from two lines characterises the angle bisector.** Let $s_1$ and $s_2$ be affine subspaces of a Euclidean affine space that meet at a point $p'$, and let $p$ be a point. Let $q_1$ and $q_2$ be the orthogonal projections of $p$ onto $s_1$ and $s_2$. Then $p$ is equidistant from $s_1$ and $s_2$, meaning $|pq_1|=|pq_2|$, if and only if $\angle pp'q_1=\angle pp'q_2$.
--
--   For two lines through $p'$, this says that the points equidistant from the lines are the points on the bisectors of the angles they form. This is the characterisation used to prove that the internal angle bisectors of a triangle meet at the incenter.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq`. Orthogonal projection onto an affine subspace requires its direction to admit orthogonal projections (automatic in finite dimensions) and the subspace to be nonempty. Nonemptiness follows from $p'\in s_i$ and is taken here as an instance argument. `∠ p p' q` is the unoriented angle at $p'$. The distance from $p$ to $s_i$ is the distance to its orthogonal projection.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.dist_orthogonalProjection_eq_iff_angle_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem angle_bisector_equidistance_6c {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p p' : P} {s₁ s₂ : AffineSubspace ℝ P} [s₁.direction.HasOrthogonalProjection]
    [s₂.direction.HasOrthogonalProjection] (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) [Nonempty s₁] [Nonempty s₂] :
    dist p (orthogonalProjection s₁ p : P) = dist p (orthogonalProjection s₂ p : P) ↔
      ∠ p p' (orthogonalProjection s₁ p : P) = ∠ p p' (orthogonalProjection s₂ p : P) := by sorry

end FamousTheorems
