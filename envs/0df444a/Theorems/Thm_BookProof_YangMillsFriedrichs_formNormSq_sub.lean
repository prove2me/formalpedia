-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_sub
-- name    : BookProof.YangMillsFriedrichs.formNormSq_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:33.881855+00:00
-- url     : https://prove2.me/theorems/06a088e6-4eac-44db-a31d-75d5ddb85ad3
-- title:
--   The Lean 4 theorem `formNormSq_sub` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_sub` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_sub
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_sub {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H) (x y : D) :
    formNormSq H (x - y)
      = formNormSq H x - 2 * (formInner H x y).re + formNormSq H y := by sorry
