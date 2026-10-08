-- Prove2me | Theorems.Thm_BookProof_ChapterH8_compress_aeval_transfer
-- name    : BookProof.ChapterH8.compress_aeval_transfer
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:32:19.915753+00:00
-- url     : https://prove2.me/theorems/d76a4250-4fcd-4da3-8970-9e56249be99c
-- title:
--   `BookProof.ChapterH8.compress_aeval_transfer` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (p :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.compress_aeval_transfer` (V : F →L[ℂ] E) (X : E →L[ℂ] E) (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F) (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (p : Polynomial ℂ) (v : E) (hv : V ((adjoint V) v) = v) : (Polynomial.aeval X p) v = V ((Polynomial.aeval (compress V X) p) ((adjoint V) v))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.compress_aeval_transfer`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.compress_aeval_transfer
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

theorem BookProof.ChapterH8.compress_aeval_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : (adjoint V).comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (p : Polynomial ℂ)
    (v : E) (hv : V ((adjoint V) v) = v) :
    (Polynomial.aeval X p) v = V ((Polynomial.aeval (compress V X) p) ((adjoint V) v)) := by sorry
