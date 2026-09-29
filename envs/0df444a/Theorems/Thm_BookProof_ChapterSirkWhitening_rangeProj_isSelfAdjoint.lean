-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_isSelfAdjoint
-- name    : BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:11:51.114654+00:00
-- url     : https://prove2.me/theorems/77dda690-fb96-4e5b-8ab3-6bd6fdb622cd
-- title:
--   (V : F →L[ℂ] E) : IsSelfAdjoint (rangeProj V)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_isSelfAdjoint (V : F →L[ℂ] E) : IsSelfAdjoint (rangeProj V) := by sorry
