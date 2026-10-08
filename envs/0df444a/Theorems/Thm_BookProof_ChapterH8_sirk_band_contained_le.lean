-- Prove2me | Theorems.Thm_BookProof_ChapterH8_sirk_band_contained_le
-- name    : BookProof.ChapterH8.sirk_band_contained_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T17:08:46.865026+00:00
-- url     : https://prove2.me/theorems/c3df1908-5154-44f4-a6f4-e82ef7989ea1
-- title:
--   The Lean 4 theorem `sirk_band_contained_le` in the `ChapterH8` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sirk_band_contained_le` in the `ChapterH8` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterH8.lean

-- Generated from ChapterH8.lean — theorem BookProof.ChapterH8.sirk_band_contained_le
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

theorem BookProof.ChapterH8.sirk_band_contained_le (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n)
      ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m) := by sorry
