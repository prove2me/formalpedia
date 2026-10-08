-- Prove2me | Theorems.Thm_BookProof_ChapterH8_compress_inv_transfer_apply
-- name    : BookProof.ChapterH8.compress_inv_transfer_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:30:20.126916+00:00
-- url     : https://prove2.me/theorems/1c135c0f-0e6d-4fcc-b79b-8845c01f8ce6
-- title:
--   `BookProof.ChapterH8.compress_inv_transfer_apply` (V : F →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (hinv : ∀ x : F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.compress_inv_transfer_apply` (V : F →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F) (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (hinv : ∀ x : F, ∃ y : F, qX (V x) = V y) (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E) (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F) (v : E) (hv : V ((adjoint V) v) = v) : qXinv v = V (qBinv ((adjoint V) v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.compress_inv_transfer_apply`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.compress_inv_transfer_apply
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH4
open BookProof.ChapterH4
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open ContinuousLinearMap

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterH8.compress_inv_transfer_apply (V : F →L[ℂ] E) (qX qXinv : E →L[ℂ] E) (qBinv : F →L[ℂ] F)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, qX (V x) = V y)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : (compress V qX).comp qBinv = ContinuousLinearMap.id ℂ F)
    (v : E) (hv : V ((adjoint V) v) = v) :
    qXinv v = V (qBinv ((adjoint V) v)) := by sorry
