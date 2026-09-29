-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_add_smul
-- name    : BookProof.YangMillsFriedrichs.formNormSq_add_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:24.226476+00:00
-- url     : https://prove2.me/theorems/ba0b097c-c0e8-416f-a1d0-558a345d1601
-- title:
--   The Lean 4 theorem `formNormSq_add_smul` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_add_smul` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_add_smul
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_add_smul {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H) (t : ℝ) (x y : D) :
    formNormSq H (x + (t : ℂ) • y)
      = formNormSq H x + 2 * t * (formInner H x y).re + t ^ 2 * formNormSq H y := by sorry
