-- Prove2me | Theorems.Thm_ChapterTotalVariance_within_le_variance
-- name    : ChapterTotalVariance.within_le_variance
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:21.205447+00:00
-- url     : https://prove2.me/theorems/72d0a1ba-93fb-472e-8714-807c3c179d53
-- title:
--   `ChapterTotalVariance.within_le_variance` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : within w X Y ≤ variance w Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.within_le_variance` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : within w X Y ≤ variance w Y
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.within_le_variance`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.within_le_variance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.within_le_variance [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    within w X Y ≤ variance w Y := by sorry
