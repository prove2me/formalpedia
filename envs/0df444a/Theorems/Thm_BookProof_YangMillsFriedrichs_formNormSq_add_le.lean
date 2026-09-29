-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_add_le
-- name    : BookProof.YangMillsFriedrichs.formNormSq_add_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:17.444986+00:00
-- url     : https://prove2.me/theorems/e35ffc87-c4de-48f6-8b12-9edf04a7e63b
-- title:
--   The Lean 4 theorem `formNormSq_add_le` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_add_le` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_add_le
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_add_le {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) (x y : D) :
    formNormSq H (x + y) ≤ 2 * formNormSq H x + 2 * formNormSq H y := by sorry
