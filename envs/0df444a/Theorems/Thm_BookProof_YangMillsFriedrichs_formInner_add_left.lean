-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formInner_add_left
-- name    : BookProof.YangMillsFriedrichs.formInner_add_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:03.148098+00:00
-- url     : https://prove2.me/theorems/f1c728f1-69b4-451e-826a-0fc0ca0d7a2e
-- title:
--   The Lean 4 theorem `formInner_add_left` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formInner_add_left` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formInner_add_left
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formInner_add_left (H : D →ₗ[ℂ] F) (x y z : D) :
    formInner H (x + y) z = formInner H x z + formInner H y z := by sorry
