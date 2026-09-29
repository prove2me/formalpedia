-- Prove2me | Theorems.Thm_BookProof_ChapterH4_compress_inv_transfer
-- name    : BookProof.ChapterH4.compress_inv_transfer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:38:58.752638+00:00
-- url     : https://prove2.me/theorems/5921c66b-d05c-47f4-97d8-44d3b4bba216
-- title:
--   (V : F →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qB qBinv : F →L[ℂ] F) (hintertwine : qX.comp V = V.comp qB) (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E) (hqBr : qB.comp qBinv =...
-- statement:
--   Lean 4 theorem `BookProof.ChapterH4.compress_inv_transfer` (module `BookProof.ChapterH4`), source chapter `BookProof/ChapterChapterH4.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH4.lean

-- Generated from ChapterH4.lean — theorem BookProof.ChapterH4.compress_inv_transfer
import Mathlib
import Definitions.Def_ChapterH4
open BookProof.ChapterH4









open scoped BigOperators


noncomputable section





variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in

theorem BookProof.ChapterH4.compress_inv_transfer (V : F →L[ℂ] E)
    (qX qXinv : E →L[ℂ] E) (qB qBinv : F →L[ℂ] F)
    (hintertwine : qX.comp V = V.comp qB)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : qB.comp qBinv = ContinuousLinearMap.id ℂ F) :
    qXinv.comp V = V.comp qBinv := by sorry
