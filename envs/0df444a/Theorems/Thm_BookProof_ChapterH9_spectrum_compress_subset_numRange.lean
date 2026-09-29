-- Prove2me | Theorems.Thm_BookProof_ChapterH9_spectrum_compress_subset_numRange
-- name    : BookProof.ChapterH9.spectrum_compress_subset_numRange
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:20:54.352986+00:00
-- url     : https://prove2.me/theorems/14c1ae82-ab17-4648-90cd-d9e69d1aa69e
-- title:
--   The Lean 4 theorem `spectrum_compress_subset_numRange` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `spectrum_compress_subset_numRange` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.spectrum_compress_subset_numRange
import Mathlib
import Definitions.Def_ChapterH9
open BookProof.ChapterH9


noncomputable section


open BookProof.ChapterH1 BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6
open BookProof.ChapterH8
open ContinuousLinearMap


variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem BookProof.ChapterH9.spectrum_compress_subset_numRange [FiniteDimensional ℂ F] (V : F →L[ℂ] E)
    (X : E →L[ℂ] E) (hViso : ∀ x : F, ‖V x‖ = ‖x‖) :
    spectrum ℂ ((compress V X : F →ₗ[ℂ] F)) ⊆ numRange X := by sorry
