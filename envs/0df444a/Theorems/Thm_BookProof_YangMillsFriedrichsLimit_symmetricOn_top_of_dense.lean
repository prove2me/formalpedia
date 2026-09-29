-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_symmetricOn_top_of_dense
-- name    : BookProof.YangMillsFriedrichsLimit.symmetricOn_top_of_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:52.624336+00:00
-- url     : https://prove2.me/theorems/5cca8e92-f63b-47f3-973e-72f71e511ee4
-- title:
--   The Lean 4 theorem `symmetricOn_top_of_dense` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `symmetricOn_top_of_dense` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.symmetricOn_top_of_dense
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.symmetricOn_top_of_dense {D : Submodule ℂ F} (A : F →L[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : ∀ x y : D, (inner ℂ (A (x : F)) (y : F) : ℂ)
      = inner ℂ (x : F) (A (y : F))) :
    SymmetricOn (⊤ : Submodule ℂ F) (topRestrict A) := by sorry
