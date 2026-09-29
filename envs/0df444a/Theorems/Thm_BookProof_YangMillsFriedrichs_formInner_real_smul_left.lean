-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formInner_real_smul_left
-- name    : BookProof.YangMillsFriedrichs.formInner_real_smul_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:34.270269+00:00
-- url     : https://prove2.me/theorems/d8a48f36-f799-42db-a81c-2e8b4ad5dfbb
-- title:
--   The Lean 4 theorem `formInner_real_smul_left` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formInner_real_smul_left` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formInner_real_smul_left
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formInner_real_smul_left (H : D →ₗ[ℂ] F) (t : ℝ) (x y : D) :
    formInner H ((t : ℂ) • x) y = (t : ℂ) * formInner H x y := by sorry
