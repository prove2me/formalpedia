-- Prove2me | Theorems.Thm_BookProof_ChapterH9_numRange_compress_subset
-- name    : BookProof.ChapterH9.numRange_compress_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:22:48.317036+00:00
-- url     : https://prove2.me/theorems/f456300b-1e4a-401b-8b8d-3a551f4f6d23
-- title:
--   (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : numRange (compress V X) ⊆ numRange X
-- statement:
--   Lean 4 theorem `BookProof.ChapterH9.numRange_compress_subset` (module `BookProof.ChapterH9`), source chapter `BookProof/ChapterChapterH9.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.numRange_compress_subset
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9 BookProof.ChapterH4

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in

theorem BookProof.ChapterH9.numRange_compress_subset (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : numRange (compress V X) ⊆ numRange X := by sorry
