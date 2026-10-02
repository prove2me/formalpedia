-- Prove2me | Theorems.Thm_BookProof_ChapterH8_adjoint_compress
-- name    : BookProof.ChapterH8.adjoint_compress
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:18:56.40873+00:00
-- url     : https://prove2.me/theorems/b745203b-fcb4-4572-8282-be48442f987e
-- title:
--   The Lean 4 theorem `adjoint_compress` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `adjoint_compress` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.adjoint_compress
import Mathlib
import Definitions.Def_ChapterH8
open BookProof.ChapterH8

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

open ContinuousLinearMap in

theorem BookProof.ChapterH8.adjoint_compress (V : F →L[ℂ] E) (X : E →L[ℂ] E) :
    adjoint (compress V X) = compress V (adjoint X) := by sorry
