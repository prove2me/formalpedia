-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_eq
-- name    : BookProof.YangMillsFriedrichs.formNormSq_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:37.491325+00:00
-- url     : https://prove2.me/theorems/2e7fa9b2-edfb-4b50-bd09-d8318399bb0b
-- title:
--   The Lean 4 theorem `formNormSq_eq` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_eq` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_eq
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_eq (H : D →ₗ[ℂ] F) (x : D) :
    formNormSq H x = ‖(x : F)‖ ^ 2 + quadForm H x := by sorry
