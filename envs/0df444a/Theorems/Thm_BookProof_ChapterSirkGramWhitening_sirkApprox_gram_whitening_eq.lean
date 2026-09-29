-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_sirkApprox_gram_whitening_eq
-- name    : BookProof.ChapterSirkGramWhitening.sirkApprox_gram_whitening_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:41.314617+00:00
-- url     : https://prove2.me/theorems/0b5f8ea0-8c5b-48ac-a9ac-186d8749af1b
-- title:
--   {m : ℕ} (w : Fin m → E) (X : E →L[ℂ] E) {T₁ T₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT₁ : IsWhitening w T₁) (hT₂ : IsWhitening w T₂) (hs₁ :...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.sirkApprox_gram_whitening_eq` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.sirkApprox_gram_whitening_eq
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.sirkApprox_gram_whitening_eq {m : ℕ} (w : Fin m → E) (X : E →L[ℂ] E)
    {T₁ T₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT₁ : IsWhitening w T₁) (hT₂ : IsWhitening w T₂)
    (hs₁ : Function.Surjective T₁) (hs₂ : Function.Surjective T₂) :
    (whitened w T₁).comp ((compress (whitened w T₁) X).comp
        (ContinuousLinearMap.adjoint (whitened w T₁)))
      = (whitened w T₂).comp ((compress (whitened w T₂) X).comp
        (ContinuousLinearMap.adjoint (whitened w T₂))) := by sorry
