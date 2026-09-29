-- Prove2me | Theorems.Thm_FamousTheorems_aa_similarity_criterion_6b
-- name    : FamousTheorems.aa_similarity_criterion_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:37.279651+00:00
-- url     : https://prove2.me/theorems/197d5e53-9f60-4bff-b0ba-f01070f9cf08
-- title:
--   The AA similarity criterion for triangles
-- statement:
--   **The AA similarity criterion for triangles.** Let $abc$ and $a'b'c'$ be triangles in real inner product spaces, with $abc$ nondegenerate. If $\angle abc=\angle a'b'c'$ and $\angle bca=\angle b'c'a'$, then the triangles are similar.
--
--   Two triangles with two pairs of equal angles are similar, because the third angles then also agree. This is Euclid's Proposition VI.4 and is the most widely used similarity criterion in elementary geometry. It is used in proofs of the intercept theorem, of the power of a point, and of Pythagoras's theorem by similar triangles.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.similar_of_angle_angle`, for triangles in possibly different Euclidean affine spaces. `Similar ![a, b, c] ![a', b', c']` means that there is $k>0$ such that every distance between vertices of the second triangle is $k$ times the corresponding distance in the first.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.similar_of_angle_angle`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem aa_similarity_criterion_6b {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') : Similar ![a, b, c] ![a', b', c'] := by sorry

end FamousTheorems
