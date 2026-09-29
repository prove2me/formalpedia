-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formInner_real_smul_right
-- name    : BookProof.YangMillsFriedrichs.formInner_real_smul_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:47.623435+00:00
-- url     : https://prove2.me/theorems/2dc653b6-06ef-4d1b-b1e1-e52cd2ce1a91
-- title:
--   The Lean 4 theorem `formInner_real_smul_right` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formInner_real_smul_right` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formInner_real_smul_right
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formInner_real_smul_right (H : D →ₗ[ℂ] F) (t : ℝ) (x y : D) :
    formInner H x ((t : ℂ) • y) = (t : ℂ) * formInner H x y := by sorry
