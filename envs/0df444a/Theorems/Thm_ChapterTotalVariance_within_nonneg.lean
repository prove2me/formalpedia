-- Prove2me | Theorems.Thm_ChapterTotalVariance_within_nonneg
-- name    : ChapterTotalVariance.within_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:00.816985+00:00
-- url     : https://prove2.me/theorems/98352125-6c0e-4f83-9528-baccf891bb6c
-- title:
--   `ChapterTotalVariance.within_nonneg` (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ within w X Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.within_nonneg` (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ within w X Y
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.within_nonneg`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.within_nonneg
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.within_nonneg (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    0 ≤ within w X Y := by sorry
