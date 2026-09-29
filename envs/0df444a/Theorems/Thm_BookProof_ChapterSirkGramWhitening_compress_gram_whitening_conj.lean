-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_compress_gram_whitening_conj
-- name    : BookProof.ChapterSirkGramWhitening.compress_gram_whitening_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:52.26799+00:00
-- url     : https://prove2.me/theorems/aff2fad2-85f9-4941-9b9b-f1559163b8a7
-- title:
--   {m : ℕ} (w : Fin m → E) (X : E →L[ℂ] E) {T₁ T₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT₂ : IsWhitening w T₂) (hs₁ : Function.Surjective T₁)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.compress_gram_whitening_conj` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.compress_gram_whitening_conj
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening
open BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.compress_gram_whitening_conj {m : ℕ} (w : Fin m → E) (X : E →L[ℂ] E)
    {T₁ T₂ : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT₂ : IsWhitening w T₂) (hs₁ : Function.Surjective T₁) (hs₂ : Function.Surjective T₂) :
    compress (whitened w T₁) X
      = (whiteningEquiv (whitened w T₂) (whitened w T₁)).comp
        ((compress (whitened w T₂) X).comp
          (whiteningEquiv (whitened w T₁) (whitened w T₂))) := by sorry
