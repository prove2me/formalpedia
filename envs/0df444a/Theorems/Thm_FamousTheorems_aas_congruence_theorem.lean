-- Prove2me | Theorems.Thm_FamousTheorems_aas_congruence_theorem
-- name    : FamousTheorems.aas_congruence_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:41.579199+00:00
-- url     : https://prove2.me/theorems/4339155a-9313-452c-a959-22088c72b7a2
-- title:
--   The AAS congruence theorem
-- statement:
--   **The AAS congruence theorem.** Let $abc$ and $a'b'c'$ be triangles, with $abc$ nondegenerate. If $\angle abc=\angle a'b'c'$, $\angle bca=\angle b'c'a'$ and $ca=c'a'$, then the triangles are congruent.
--
--   Two triangles with two equal angles and an equal side opposite one of them are congruent. This is the second part of Euclid's Proposition I.26.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.angle_angle_side`, for triangles in possibly different real inner product spaces. `Congruent ![a, b, c] ![a', b', c']` means that corresponding pairwise distances agree.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.angle_angle_side`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem aas_congruence_theorem {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') (h₃ : dist c a = dist c' a') : Congruent ![a, b, c] ![a', b', c'] := by sorry

end FamousTheorems
