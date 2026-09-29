-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_topRestrict_apply
-- name    : BookProof.YangMillsFriedrichsLimit.topRestrict_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:59.063954+00:00
-- url     : https://prove2.me/theorems/9d23b406-a399-45bc-b72e-06b0f34a06b9
-- title:
--   The Lean 4 theorem `topRestrict_apply` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `topRestrict_apply` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.topRestrict_apply
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.topRestrict_apply (A : F →L[ℂ] F) (x : (⊤ : Submodule ℂ F)) :
    topRestrict A x = A (x : F) := by sorry
