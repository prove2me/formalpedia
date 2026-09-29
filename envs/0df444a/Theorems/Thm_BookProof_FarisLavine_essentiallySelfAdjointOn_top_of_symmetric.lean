-- Prove2me | Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_top_of_symmetric
-- name    : BookProof.FarisLavine.essentiallySelfAdjointOn_top_of_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:19:20.83976+00:00
-- url     : https://prove2.me/theorems/7c8efed6-0d86-4d3c-83f6-3d942a377d7a
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_top_of_symmetric` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_top_of_symmetric` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.essentiallySelfAdjointOn_top_of_symmetric
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.essentiallySelfAdjointOn_top_of_symmetric [CompleteSpace F]
    (H : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hH : SymmetricOn ⊤ H) :
    EssentiallySelfAdjointOn (⊤ : Submodule ℂ F) H := by sorry
