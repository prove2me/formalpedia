-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_compression_block_le
-- name    : BookProof.ChapterH8.sirk_compression_block_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:25:45.953993+00:00
-- url     : https://prove2.me/theorems/7e5d59af-74dd-4832-b38b-f0ecb0aa29c8
-- title:
--   The Lean 4 theorem `sirk_compression_block_le` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_block_le` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_compression_block_le
import Mathlib
import Definitions.Def_ChapterH8
open BookProof.ChapterH8

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

theorem BookProof.ChapterH8.sirk_compression_block_le {m n : ℕ} (hmn : m ≤ n) (X : E →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin m) →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (hnest : ∀ i : Fin m, Vm (EuclideanSpace.single i (1 : ℂ))
      = Vn (EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ)))
    (i j : Fin m) :
    reduceGenerator m Vm X i j
      = reduceGenerator n Vn X (Fin.castLE hmn i) (Fin.castLE hmn j) := by sorry
