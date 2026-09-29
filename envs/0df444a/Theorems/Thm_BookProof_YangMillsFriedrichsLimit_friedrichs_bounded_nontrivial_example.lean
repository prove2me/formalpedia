-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_friedrichs_bounded_nontrivial_example
-- name    : BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_nontrivial_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:03.95107+00:00
-- url     : https://prove2.me/theorems/9cc41678-7e2d-4b9b-b72b-6d5e0c0ce95b
-- title:
--   The Lean 4 theorem `friedrichs_bounded_nontrivial_example` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `friedrichs_bounded_nontrivial_example` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_nontrivial_example
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.friedrichs_bounded_nontrivial_example [CompleteSpace F] (D : Submodule ℂ F)
    (hdense : Dense (D : Set F)) :
    ∃ A : F →L[ℂ] F, (∀ x : D, A (x : F) = D.subtype x) ∧
      IsPositiveSelfAdjointExtension (D.subtype) (topRestrict A) := by sorry
