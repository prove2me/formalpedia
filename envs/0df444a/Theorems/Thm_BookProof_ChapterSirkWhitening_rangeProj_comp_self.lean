-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_comp_self
-- name    : BookProof.ChapterSirkWhitening.rangeProj_comp_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:53:49.091142+00:00
-- url     : https://prove2.me/theorems/65e8d05e-1ad4-47d8-8339-f506a9ff2803
-- title:
--   (V : F →L[ℂ] E) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) : (rangeProj V).comp (rangeProj V) = rangeProj V
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_comp_self` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_comp_self
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_comp_self (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (rangeProj V).comp (rangeProj V) = rangeProj V := by sorry
