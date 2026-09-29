-- Prove2me | Theorems.Thm_BookProof_ChapterSirkTruncation_compress_comp
-- name    : BookProof.ChapterSirkTruncation.compress_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:36:27.579748+00:00
-- url     : https://prove2.me/theorems/2dddd078-632b-4fc5-bb2b-318b5e3cef15
-- title:
--   (V : F →L[ℂ] E) (W : G →L[ℂ] F) (X : E →L[ℂ] E) : compress (V.comp W) X = compress W (compress V X)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkTruncation.compress_comp` (module `BookProof.ChapterSirkTruncation`), source chapter `BookProof/ChapterChapterSirkTruncation.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkTruncation.lean

-- Generated from ChapterSirkTruncation.lean — theorem BookProof.ChapterSirkTruncation.compress_comp
import Mathlib
import Definitions.Def_ChapterSirkTruncation
open BookProof.ChapterSirkTruncation








noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterSirkEndToEnd
open BookProof.ChapterSirkWhitening

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkTruncation.compress_comp (V : F →L[ℂ] E) (W : G →L[ℂ] F) (X : E →L[ℂ] E) :
    compress (V.comp W) X = compress W (compress V X) := by sorry
