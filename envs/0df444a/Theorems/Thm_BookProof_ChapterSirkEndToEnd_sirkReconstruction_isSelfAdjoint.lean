-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_sirkReconstruction_isSelfAdjoint
-- name    : BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:47:24.070985+00:00
-- url     : https://prove2.me/theorems/e7423595-6da5-4dfd-ad16-2477b98ba466
-- title:
--   (V : F →L[ℂ] E) : IsSelfAdjoint (sirkReconstruction V)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.sirkReconstruction_isSelfAdjoint (V : F →L[ℂ] E) :
    IsSelfAdjoint (sirkReconstruction V) := by sorry
