-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_compress_reconstruct_eq
-- name    : BookProof.ChapterSirkWhitening.compress_reconstruct_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:49:50.70465+00:00
-- url     : https://prove2.me/theorems/92cf5083-cdb0-4d0e-8e71-95b4937950e1
-- title:
--   (V : F →L[ℂ] E) (X : E →L[ℂ] E) : V.comp ((compress V X).comp V.adjoint) = (rangeProj V).comp (X.comp (rangeProj V))
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.compress_reconstruct_eq` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.compress_reconstruct_eq
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.compress_reconstruct_eq (V : F →L[ℂ] E) (X : E →L[ℂ] E) :
    V.comp ((compress V X).comp V.adjoint) = (rangeProj V).comp (X.comp (rangeProj V)) := by sorry
