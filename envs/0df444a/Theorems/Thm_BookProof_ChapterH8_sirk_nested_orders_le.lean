-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_nested_orders_le
-- name    : BookProof.ChapterH8.sirk_nested_orders_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:07:13.204718+00:00
-- url     : https://prove2.me/theorems/4a129f5d-b043-46e9-a5f7-31ab9f541183
-- title:
--   The Lean 4 theorem `sirk_nested_orders_le` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_nested_orders_le` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_nested_orders_le
import Definitions.Def_ChapterH4
import Mathlib
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
open BookProof.ChapterH5
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

theorem BookProof.ChapterH8.sirk_nested_orders_le {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (H : E →ₗ[K] E) (v : E) (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) {m n : ℕ} (hmn : m ≤ n) :
    krylovSpan H v m ≤ krylovSpan H v n
      ∧ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n)
          ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m) := by sorry
