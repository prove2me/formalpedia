-- Prove2me | Theorems.Thm_BookProof_ChapterH8_adjoint_pow
-- name    : BookProof.ChapterH8.adjoint_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:23:31.447985+00:00
-- url     : https://prove2.me/theorems/c30f9519-b74f-4397-a0fb-08f47fdb3275
-- title:
--   The Lean 4 theorem `adjoint_pow` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `adjoint_pow` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.adjoint_pow
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

theorem BookProof.ChapterH8.adjoint_pow (A : F →L[ℂ] F) (k : ℕ) : adjoint (A ^ k) = (adjoint A) ^ k := by sorry
