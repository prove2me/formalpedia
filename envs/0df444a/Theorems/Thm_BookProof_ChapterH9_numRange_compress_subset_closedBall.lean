-- Prove2me | Theorems.Thm_BookProof_ChapterH9_numRange_compress_subset_closedBall
-- name    : BookProof.ChapterH9.numRange_compress_subset_closedBall
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T13:39:24.26591+00:00
-- url     : https://prove2.me/theorems/36456cd6-2ba2-4d42-9367-c244ea15cf02
-- title:
--   The Lean 4 theorem `numRange_compress_subset_closedBall` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `numRange_compress_subset_closedBall` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.numRange_compress_subset_closedBall
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

theorem BookProof.ChapterH9.numRange_compress_subset_closedBall (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    numRange (compress V X) ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by sorry
