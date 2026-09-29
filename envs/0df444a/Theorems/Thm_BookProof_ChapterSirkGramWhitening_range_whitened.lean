-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_whitened
-- name    : BookProof.ChapterSirkGramWhitening.range_whitened
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:04:45.559374+00:00
-- url     : https://prove2.me/theorems/584a2d59-a027-4a49-806c-61975c27d417
-- title:
--   {m : ℕ} (w : Fin m → E) {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)} (hT : Function.Surjective T) : LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.range_whitened` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.range_whitened
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.range_whitened {m : ℕ} (w : Fin m → E)
    {T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)}
    (hT : Function.Surjective T) :
    LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by sorry
