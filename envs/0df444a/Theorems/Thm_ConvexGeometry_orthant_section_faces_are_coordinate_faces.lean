-- Prove2me | Theorems.Thm_ConvexGeometry_orthant_section_faces_are_coordinate_faces
-- name    : ConvexGeometry.orthant_section_faces_are_coordinate_faces
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-22T15:11:07.558458+00:00
-- url     : https://prove2.me/theorems/053dd816-08cd-4700-a729-3623df792e52
-- title:
--   Faces of nonnegative subspace sections are coordinate faces
-- statement:
--   Let K be an ordered field, I a finite coordinate set, and L a linear subspace of K^I. Intersect L with the nonnegative orthant. Every face of this pointed cone is obtained by requiring a set of coordinates to vanish, and every such coordinate-zero section is a face. The statement also applies when the section has lower dimension or redundant coordinate constraints.
-- source:
--   A self-contained finite-dimensional proof using the face property of a pointed cone. A point of maximal coordinate support is formed by summing one witness for each coordinate used by the face; coordinatewise nonnegativity prevents cancellation. A small positive multiple then establishes the reverse inclusion.

import Mathlib

namespace ConvexGeometry

theorem orthant_section_faces_are_coordinate_faces {𝕜 ι : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ↔
      ∃ B : Set ι, ∀ x : ι → 𝕜,
        (x ∈ F ↔
          x ∈ (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ∧
            ∀ i, i ∉ B → x i = 0) := by
  sorry

end ConvexGeometry
