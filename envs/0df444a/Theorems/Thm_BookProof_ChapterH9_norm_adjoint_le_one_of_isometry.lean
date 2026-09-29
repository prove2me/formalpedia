-- Prove2me | Theorems.Thm_BookProof_ChapterH9_norm_adjoint_le_one_of_isometry
-- name    : BookProof.ChapterH9.norm_adjoint_le_one_of_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:34.447086+00:00
-- url     : https://prove2.me/theorems/3f1b4292-36e7-43ce-925f-5d86be38c1ce
-- title:
--   The Lean 4 theorem `norm_adjoint_le_one_of_isometry` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_adjoint_le_one_of_isometry` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.norm_adjoint_le_one_of_isometry
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.norm_adjoint_le_one_of_isometry (V : F →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    ‖adjoint V‖ ≤ 1 := by sorry
