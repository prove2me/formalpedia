-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_adjoint
-- name    : BookProof.ChapterSirkWhitening.rangeProj_adjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:52:03.568891+00:00
-- url     : https://prove2.me/theorems/512514fa-8c44-42be-91d0-9052f2b9e960
-- title:
--   (V : F →L[ℂ] E) : ContinuousLinearMap.adjoint (rangeProj V) = rangeProj V
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_adjoint` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_adjoint
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_adjoint (V : F →L[ℂ] E) :
    ContinuousLinearMap.adjoint (rangeProj V) = rangeProj V := by sorry
