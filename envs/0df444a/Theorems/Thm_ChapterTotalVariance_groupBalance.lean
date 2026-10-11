-- Prove2me | Theorems.Thm_ChapterTotalVariance_groupBalance
-- name    : ChapterTotalVariance.groupBalance
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:14.170677+00:00
-- url     : https://prove2.me/theorems/f6f24558-11d7-4544-8bea-9b6bfd412778
-- title:
--   `ChapterTotalVariance.groupBalance` (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : κ) : (∑ ω, if X ω = g then w ω * (Y ω - condMean w X Y g) else 0) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.groupBalance` (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (g : κ) : (∑ ω, if X ω = g then w ω * (Y ω - condMean w X Y g) else 0) = 0
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.groupBalance`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.groupBalance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.groupBalance (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (g : κ) :
    (∑ ω, if X ω = g then w ω * (Y ω - condMean w X Y g) else 0) = 0 := by sorry
