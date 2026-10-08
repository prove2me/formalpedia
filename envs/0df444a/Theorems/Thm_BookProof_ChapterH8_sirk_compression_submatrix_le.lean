-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_compression_submatrix_le
-- name    : BookProof.ChapterH8.sirk_compression_submatrix_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:26:58.036378+00:00
-- url     : https://prove2.me/theorems/57a1f7a4-86bb-4b50-9db4-0ada68ac0a29
-- title:
--   The Lean 4 theorem `sirk_compression_submatrix_le` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_submatrix_le` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_compression_submatrix_le
import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH6
open BookProof.ChapterH6
open BookProof.ChapterH8

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

theorem BookProof.ChapterH8.sirk_compression_submatrix_le {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin m) →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (hnest : ∀ i : Fin m, Vm (EuclideanSpace.single i (1 : ℂ))
      = Vn (EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ))) :
    reduceGenerator m Vm X
      = (reduceGenerator n Vn X).submatrix (Fin.castLE hmn) (Fin.castLE hmn) := by sorry
