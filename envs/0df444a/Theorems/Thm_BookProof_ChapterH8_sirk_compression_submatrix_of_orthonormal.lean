-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_compression_submatrix_of_orthonormal
-- name    : BookProof.ChapterH8.sirk_compression_submatrix_of_orthonormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:49:52.480239+00:00
-- url     : https://prove2.me/theorems/63c07d46-d922-42cc-a6c9-5a79d1105bb9
-- title:
--   The Lean 4 theorem `sirk_compression_submatrix_of_orthonormal` in the `ChapterH8Bases` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_submatrix_of_orthonormal` in the `ChapterH8Bases` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8Bases.lean

-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.sirk_compression_submatrix_of_orthonormal
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterH6
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

theorem BookProof.ChapterH8.sirk_compression_submatrix_of_orthonormal {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (w : Fin m → E) (w' : Fin n → E) (hw : Orthonormal ℂ w) (hw' : Orthonormal ℂ w')
    (hnest : ∀ i : Fin m, w i = w' (Fin.castLE hmn i)) :
    reduceGenerator m (orthonormalEmbedding w hw) X
      = (reduceGenerator n (orthonormalEmbedding w' hw') X).submatrix
          (Fin.castLE hmn) (Fin.castLE hmn) := by sorry
