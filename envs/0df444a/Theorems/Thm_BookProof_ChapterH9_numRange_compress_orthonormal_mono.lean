-- Prove2me | Theorems.Thm_BookProof_ChapterH9_numRange_compress_orthonormal_mono
-- name    : BookProof.ChapterH9.numRange_compress_orthonormal_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:22:23.402987+00:00
-- url     : https://prove2.me/theorems/25194774-ae7f-4276-8801-6b09a254761e
-- title:
--   The Lean 4 theorem `numRange_compress_orthonormal_mono` in the `ChapterH9` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `numRange_compress_orthonormal_mono` in the `ChapterH9` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH9.lean

-- Generated from ChapterH9.lean — theorem BookProof.ChapterH9.numRange_compress_orthonormal_mono
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

theorem BookProof.ChapterH9.numRange_compress_orthonormal_mono {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    numRange (compress (orthonormalEmbedding w hw) X)
      ⊆ numRange (compress (orthonormalEmbedding w' hw') X) := by sorry
