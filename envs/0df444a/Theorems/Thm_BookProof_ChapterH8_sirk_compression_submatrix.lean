-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_compression_submatrix
-- name    : BookProof.ChapterH8.sirk_compression_submatrix
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:26:34.079898+00:00
-- url     : https://prove2.me/theorems/f6985d48-5769-411b-978a-8cef5872bfd5
-- title:
--   The Lean 4 theorem `sirk_compression_submatrix` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_submatrix` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_compression_submatrix
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

theorem BookProof.ChapterH8.sirk_compression_submatrix (n : ℕ) (X : E →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] E)
    (hnest : ∀ i : Fin n, Vn (EuclideanSpace.single i (1 : ℂ))
      = Vm (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ))) :
    reduceGenerator n Vn X
      = (reduceGenerator (n + 1) Vm X).submatrix Fin.castSucc Fin.castSucc := by sorry
