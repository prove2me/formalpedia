-- Prove2me | Theorems.Thm_ChapterTotalVariance_between_nonneg
-- name    : ChapterTotalVariance.between_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:57.122466+00:00
-- url     : https://prove2.me/theorems/18b14dd8-68d5-4ff7-be23-1037cb4a6310
-- title:
--   `ChapterTotalVariance.between_nonneg` (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ between w X Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.between_nonneg` (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ between w X Y
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.between_nonneg`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.between_nonneg
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.between_nonneg (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    0 ≤ between w X Y := by sorry
