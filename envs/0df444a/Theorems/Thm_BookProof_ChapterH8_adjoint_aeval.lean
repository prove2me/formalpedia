-- Prove2me | Theorems.Thm_BookProof_ChapterH8_adjoint_aeval
-- name    : BookProof.ChapterH8.adjoint_aeval
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T17:30:13.074466+00:00
-- url     : https://prove2.me/theorems/565e7618-1416-4288-80b5-b1fa1bba4f72
-- title:
--   `BookProof.ChapterH8.adjoint_aeval` (A : F →L[ℂ] F) (p : Polynomial ℂ) : adjoint (Polynomial.aeval A p) = Polynomial.aeval (adjoint A) (p.map (starRingEnd ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH8`.
--
--   `BookProof.ChapterH8.adjoint_aeval` (A : F →L[ℂ] F) (p : Polynomial ℂ) : adjoint (Polynomial.aeval A p) = Polynomial.aeval (adjoint A) (p.map (starRingEnd ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH8.adjoint_aeval`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.adjoint_aeval
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8
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

theorem BookProof.ChapterH8.adjoint_aeval (A : F →L[ℂ] F) (p : Polynomial ℂ) :
    adjoint (Polynomial.aeval A p) = Polynomial.aeval (adjoint A) (p.map (starRingEnd ℂ)) := by sorry
