-- Prove2me | Theorems.Thm_ChapterTotalVariance_crossTerm_zero
-- name    : ChapterTotalVariance.crossTerm_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:25:41.038989+00:00
-- url     : https://prove2.me/theorems/a5131da2-63e5-4ffe-bb09-1880105e6900
-- title:
--   `ChapterTotalVariance.crossTerm_zero` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : (∑ ω, w ω * (Y ω - condMean w X Y (X ω)) * (condMean w X Y...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.crossTerm_zero` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : (∑ ω, w ω * (Y ω - condMean w X Y (X ω)) * (condMean w X Y (X ω) - mean w Y)) = 0
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.crossTerm_zero`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.crossTerm_zero
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.crossTerm_zero [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    (∑ ω, w ω * (Y ω - condMean w X Y (X ω)) * (condMean w X Y (X ω) - mean w Y))
      = 0 := by sorry
