-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_apply
-- name    : BookProof.ChapterSirkWhitening.rangeProj_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:52:44.057456+00:00
-- url     : https://prove2.me/theorems/61b51fef-0b41-4d03-be15-5d24466ada5a
-- title:
--   (V : F →L[ℂ] E) (u : E) : rangeProj V u = V (V.adjoint u)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_apply` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_apply
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_apply (V : F →L[ℂ] E) (u : E) :
    rangeProj V u = V (V.adjoint u) := by sorry
