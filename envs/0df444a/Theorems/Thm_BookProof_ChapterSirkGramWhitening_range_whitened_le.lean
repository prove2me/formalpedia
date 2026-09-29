-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramWhitening_range_whitened_le
-- name    : BookProof.ChapterSirkGramWhitening.range_whitened_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:55:49.426427+00:00
-- url     : https://prove2.me/theorems/d00e8e7e-80a5-4651-9a17-6b09a74f4e3b
-- title:
--   {m : ℕ} (w : Fin m → E) (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) : LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E) ≤ Submodule.span ℂ (Set.range w)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramWhitening.range_whitened_le` (module `BookProof.ChapterSirkGramWhitening`), source chapter `BookProof/ChapterChapterSirkGramWhitening.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramWhitening.lean

-- Generated from ChapterSirkGramWhitening.lean — theorem BookProof.ChapterSirkGramWhitening.range_whitened_le
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening








noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterSirkGramWhitening.range_whitened_le {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    LinearMap.range (whitened w T : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] E)
      ≤ Submodule.span ℂ (Set.range w) := by sorry
