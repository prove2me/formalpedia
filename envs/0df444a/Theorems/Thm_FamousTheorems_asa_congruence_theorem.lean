-- Prove2me | Theorems.Thm_FamousTheorems_asa_congruence_theorem
-- name    : FamousTheorems.asa_congruence_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:38.720976+00:00
-- url     : https://prove2.me/theorems/6bc59a71-3032-4840-8cbe-eb29f8e3cee3
-- title:
--   The ASA congruence theorem
-- statement:
--   **The ASA congruence theorem.** Let $abc$ and $a'b'c'$ be triangles, with $abc$ nondegenerate. If $\angle abc=\angle a'b'c'$, $bc=b'c'$ and $\angle bca=\angle b'c'a'$, then the triangles are congruent.
--
--   Two triangles with two equal angles and equal included side are congruent. This is Euclid's Proposition I.26 (first part) and is one of the standard triangle congruence criteria.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.angle_side_angle`, for triangles in possibly different real inner product spaces. `Congruent ![a, b, c] ![a', b', c']` means that corresponding pairwise distances agree.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.angle_side_angle`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem asa_congruence_theorem {V₁ V₂ P₁ P₂ : Type*} [NormedAddCommGroup V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₁]
    [InnerProductSpace ℝ V₂] [MetricSpace P₁] [MetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
    {a b c : P₁} {a' b' c' : P₂} (hnd : ¬Collinear ℝ ({a, b, c} : Set P₁)) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : dist b c = dist b' c') (h₃ : ∠ b c a = ∠ b' c' a') : Congruent ![a, b, c] ![a', b', c'] := by sorry

end FamousTheorems
