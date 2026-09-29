-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_nonneg
-- name    : BookProof.YangMillsFriedrichs.formNormSq_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:05.213835+00:00
-- url     : https://prove2.me/theorems/8d92dafe-9e3a-42d0-aff8-2ecabc6a27dc
-- title:
--   The Lean 4 theorem `formNormSq_nonneg` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_nonneg` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_nonneg
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_nonneg {H : D →ₗ[ℂ] F} (hpos : ∀ x : D, 0 ≤ quadForm H x) (x : D) :
    0 ≤ formNormSq H x := by sorry
