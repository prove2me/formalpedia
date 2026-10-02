-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_compression_block_op
-- name    : BookProof.ChapterH8.sirk_compression_block_op
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:25:55.967186+00:00
-- url     : https://prove2.me/theorems/ab80ef4f-3b47-4932-85fe-c9c4abbf99b9
-- title:
--   The Lean 4 theorem `sirk_compression_block_op` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_block_op` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_compression_block_op
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

theorem BookProof.ChapterH8.sirk_compression_block_op (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (X : E →L[ℂ] E) (hJ : Vn = Vm.comp J) :
    compress Vn X = (adjoint J).comp ((compress Vm X).comp J) := by sorry
