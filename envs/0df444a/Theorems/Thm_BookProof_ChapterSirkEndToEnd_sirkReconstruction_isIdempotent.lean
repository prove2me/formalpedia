-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirkReconstruction_isIdempotent
-- name    : BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:46:51.263063+00:00
-- url     : https://prove2.me/theorems/a6759d69-d829-45aa-adeb-698eed4b03f5
-- title:
--   (V : F →L[ℂ] E) (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) : (sirkReconstruction V).comp (sirkReconstruction V) = sirkReconstruction V
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirkReconstruction_isIdempotent (V : F →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) :
    (sirkReconstruction V).comp (sirkReconstruction V) = sirkReconstruction V := by sorry
