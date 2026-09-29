-- Prove2me | Theorems.Thm_BookProof_ChapterSirkWhitening_rangeProj_comp_embedding
-- name    : BookProof.ChapterSirkWhitening.rangeProj_comp_embedding
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:53:18.589744+00:00
-- url     : https://prove2.me/theorems/4eb2e543-54bc-4056-b957-6e0f9cda3ad0
-- title:
--   (V : F →L[ℂ] E) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (y : F) : rangeProj V (V y) = V y
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkWhitening.rangeProj_comp_embedding` (module `BookProof.ChapterSirkWhitening`), source chapter `BookProof/ChapterChapterSirkWhitening.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkWhitening.lean

-- Generated from ChapterSirkWhitening.lean — theorem BookProof.ChapterSirkWhitening.rangeProj_comp_embedding
import Mathlib
import Definitions.Def_ChapterSirkWhitening
open BookProof.ChapterSirkWhitening







noncomputable section


open BookProof.ChapterH4

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterSirkWhitening.rangeProj_comp_embedding (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (y : F) :
    rangeProj V (V y) = V y := by sorry
