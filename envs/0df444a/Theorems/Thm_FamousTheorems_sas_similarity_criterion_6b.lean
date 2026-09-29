-- Prove2me | Theorems.Thm_FamousTheorems_sas_similarity_criterion_6b
-- name    : FamousTheorems.sas_similarity_criterion_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:45.397975+00:00
-- url     : https://prove2.me/theorems/aca844e9-ab4d-4b67-8f5d-92431f0c5fe8
-- title:
--   The SAS similarity criterion for triangles
-- statement:
--   **The SAS similarity criterion for triangles.** Let $abc$ and $a'b'c'$ be nondegenerate triangles in real inner product spaces. If $\angle abc=\angle a'b'c'$ and $ab:bc=a'b':b'c'$, then the triangles are similar.
--
--   Two triangles are similar when they have an equal angle and the sides enclosing it are proportional. This is Euclid's Proposition VI.6, and together with the AA and SSS criteria it is one of the three standard similarity tests.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.similar_of_side_angle_side`, for triangles in possibly different Euclidean affine spaces. The proportion is stated without division as $ab\cdot b'c'=bc\cdot a'b'$. `Similar ![a, b, c] ![a', b', c']` means that corresponding distances are proportional with a positive ratio.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.similar_of_side_angle_side`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem sas_similarity_criterion_6b {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁))
    (hnd' : ¬Collinear ℝ ({a', b', c'} : Set P₂)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : dist a b * dist b' c' = dist b c * dist a' b') : Similar ![a, b, c] ![a', b', c'] := by sorry

end FamousTheorems
