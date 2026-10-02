-- Prove2me | Theorems.Thm_BookProof_ChapterH8_adjoint_comp_self_of_nested
-- name    : BookProof.ChapterH8.adjoint_comp_self_of_nested
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:18:43.437469+00:00
-- url     : https://prove2.me/theorems/b6df429c-5fa5-483a-ac23-12dd913d08be
-- title:
--   The Lean 4 theorem `adjoint_comp_self_of_nested` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `adjoint_comp_self_of_nested` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.adjoint_comp_self_of_nested
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

theorem BookProof.ChapterH8.adjoint_comp_self_of_nested (Vn : F →L[ℂ] E) (Vm : G →L[ℂ] E) (J : F →L[ℂ] G)
    (hJ : Vn = Vm.comp J)
    (hVm : (adjoint Vm).comp Vm = ContinuousLinearMap.id ℂ G)
    (hJJ : (adjoint J).comp J = ContinuousLinearMap.id ℂ F) :
    (adjoint Vn).comp Vn = ContinuousLinearMap.id ℂ F := by sorry
