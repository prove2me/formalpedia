-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_friedrichs_of_bounded
-- name    : BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:14:50.129461+00:00
-- url     : https://prove2.me/theorems/7fec3fad-0301-4707-9d0f-2c1ae2fb33a5
-- title:
--   The Lean 4 theorem `friedrichs_of_bounded` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `friedrichs_of_bounded` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.friedrichs_of_bounded [CompleteSpace F] {D : Submodule ℂ F} (H : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) (C : ℝ) (hbd : ∀ x : D, ‖H x‖ ≤ C * ‖(x : F)‖) :
    ∃ A : F →L[ℂ] F, (∀ x : D, A (x : F) = H x) ∧
      IsPositiveSelfAdjointExtension H (topRestrict A) := by sorry
