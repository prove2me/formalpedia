-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_synthesis
-- name    : BookProof.ChapterSirkGramWhitening.range_synthesis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:28:23.791669+00:00
-- url     : https://prove2.me/theorems/a0ebc15d-d035-45f7-af52-ee04c02822a5
-- title:
--   {m : ℕ} (w : Fin m → E) : LinearMap.range (synthesis w : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) = Submodule.span ℂ (Set.range w)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.range_synthesis` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.range_synthesis
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.range_synthesis {m : ℕ} (w : Fin m → E) :
    LinearMap.range (synthesis w : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      = Submodule.span ℂ (Set.range w) := by sorry
