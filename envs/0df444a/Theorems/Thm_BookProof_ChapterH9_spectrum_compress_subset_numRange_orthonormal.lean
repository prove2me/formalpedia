-- Prove2me | Theorems.Thm_BookProof_ChapterH9_spectrum_compress_subset_numRange_orthonormal
-- name    : BookProof.ChapterH9.spectrum_compress_subset_numRange_orthonormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:23:23.360985+00:00
-- url     : https://prove2.me/theorems/af902d72-03da-4f98-969f-b2ce1293f75b
-- title:
--   The Lean 4 theorem `spectrum_compress_subset_numRange_orthonormal` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `spectrum_compress_subset_numRange_orthonormal` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.spectrum_compress_subset_numRange_orthonormal
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

theorem BookProof.ChapterH9.spectrum_compress_subset_numRange_orthonormal {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    spectrum ℂ ((compress (orthonormalEmbedding w hw) X :
        EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)))
      ⊆ numRange (compress (orthonormalEmbedding w' hw') X)
      ∩ numRange X := by sorry
