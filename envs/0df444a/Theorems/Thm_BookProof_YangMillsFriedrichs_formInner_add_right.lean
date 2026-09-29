-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formInner_add_right
-- name    : BookProof.YangMillsFriedrichs.formInner_add_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:15.993165+00:00
-- url     : https://prove2.me/theorems/e8c10e11-c3e3-4773-8c1b-99aff1f5fe1c
-- title:
--   The Lean 4 theorem `formInner_add_right` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formInner_add_right` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formInner_add_right
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formInner_add_right (H : D →ₗ[ℂ] F) (x y z : D) :
    formInner H x (y + z) = formInner H x y + formInner H x z := by sorry
