-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_compression_block
-- name    : BookProof.ChapterH8.sirk_compression_block
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T15:23:30.486212+00:00
-- url     : https://prove2.me/theorems/650b5df0-37ab-4337-8dc7-6e1ed89f009e
-- title:
--   The Lean 4 theorem `sirk_compression_block` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_compression_block` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_compression_block
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

theorem BookProof.ChapterH8.sirk_compression_block (n : ℕ) (X : E →L[ℂ] E)
    (Vn : EuclideanSpace ℂ (Fin n) →L[ℂ] E)
    (Vm : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] E)
    (hnest : ∀ i : Fin n, Vn (EuclideanSpace.single i (1 : ℂ))
      = Vm (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)))
    (i j : Fin n) :
    reduceGenerator n Vn X i j
      = reduceGenerator (n + 1) Vm X (Fin.castSucc i) (Fin.castSucc j) := by sorry
