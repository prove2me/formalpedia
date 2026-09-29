-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_add
-- name    : BookProof.YangMillsFriedrichs.formNormSq_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:28:52.792404+00:00
-- url     : https://prove2.me/theorems/c82d2738-aa8d-4b22-80cf-bcbc7b29fe48
-- title:
--   The Lean 4 theorem `formNormSq_add` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_add` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_add
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_add {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H) (x y : D) :
    formNormSq H (x + y)
      = formNormSq H x + 2 * (formInner H x y).re + formNormSq H y := by sorry
