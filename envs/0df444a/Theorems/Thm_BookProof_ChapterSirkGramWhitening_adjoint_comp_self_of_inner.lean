-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_adjoint_comp_self_of_inner
-- name    : BookProof.ChapterSirkGramWhitening.adjoint_comp_self_of_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:49:50.61527+00:00
-- url     : https://prove2.me/theorems/5bdadbae-656a-4732-bc1c-403eb4d7d571
-- title:
--   {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E) (h : ∀ c d : F, ⟪V c, V d⟫_ℂ = ⟪c, d⟫_ℂ) : (ContinuousLinearMap.adjoint V).comp V =...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.adjoint_comp_self_of_inner` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.adjoint_comp_self_of_inner
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.adjoint_comp_self_of_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (V : F →L[ℂ] E)
    (h : ∀ c d : F, ⟪V c, V d⟫_ℂ = ⟪c, d⟫_ℂ) :
    (ContinuousLinearMap.adjoint V).comp V = ContinuousLinearMap.id ℂ F := by sorry
