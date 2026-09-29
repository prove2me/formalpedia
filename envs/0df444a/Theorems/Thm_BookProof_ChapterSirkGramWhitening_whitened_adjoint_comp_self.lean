-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_whitened_adjoint_comp_self
-- name    : BookProof.ChapterSirkGramWhitening.whitened_adjoint_comp_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:49:54.723986+00:00
-- url     : https://prove2.me/theorems/aa43ec52-dd8b-4c86-9b13-35e4d1d43fc1
-- title:
--   {m : ℕ} (w : Fin m → E) {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : IsWhitening w T) : (ContinuousLinearMap.adjoint (whitened w T)).comp (whitened w T) =...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.whitened_adjoint_comp_self` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.whitened_adjoint_comp_self
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.whitened_adjoint_comp_self {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : IsWhitening w T) :
    (ContinuousLinearMap.adjoint (whitened w T)).comp (whitened w T)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by sorry
