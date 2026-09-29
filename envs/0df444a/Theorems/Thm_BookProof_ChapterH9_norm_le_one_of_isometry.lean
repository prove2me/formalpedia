-- Prove2me | Theorems.Thm_BookProof_ChapterH9_norm_le_one_of_isometry
-- name    : BookProof.ChapterH9.norm_le_one_of_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:35:30.565975+00:00
-- url     : https://prove2.me/theorems/91030772-e883-4821-ba5e-84131277520a
-- title:
--   The Lean 4 theorem `norm_le_one_of_isometry` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_le_one_of_isometry` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.norm_le_one_of_isometry
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

omit [CompleteSpace E] [CompleteSpace F] in

theorem BookProof.ChapterH9.norm_le_one_of_isometry (V : F →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    ‖V‖ ≤ 1 := by sorry
