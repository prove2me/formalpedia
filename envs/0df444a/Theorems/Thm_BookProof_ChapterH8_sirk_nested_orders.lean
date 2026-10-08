-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_nested_orders
-- name    : BookProof.ChapterH8.sirk_nested_orders
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T03:13:55.92451+00:00
-- url     : https://prove2.me/theorems/29b21b54-23d5-43dd-941d-383976cf81d0
-- title:
--   The Lean 4 theorem `sirk_nested_orders` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_nested_orders` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_nested_orders
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

theorem BookProof.ChapterH8.sirk_nested_orders {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (H : E →ₗ[K] E) (v : E) (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) :
    ∀ n : ℕ, krylovSpan H v n ≤ krylovSpan H v (n + 1)
      ∧ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv (n + 1))
          ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n) := by sorry
