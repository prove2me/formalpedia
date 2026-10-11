-- Prove2me | Theorems.Thm_ChapterTotalVariance_between_le_variance
-- name    : ChapterTotalVariance.between_le_variance
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:58.742166+00:00
-- url     : https://prove2.me/theorems/65596d8d-3b1f-4764-a413-04724a6459af
-- title:
--   `ChapterTotalVariance.between_le_variance` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : between w X Y ≤ variance w Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.between_le_variance` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : between w X Y ≤ variance w Y
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.between_le_variance`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.between_le_variance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.between_le_variance [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    between w X Y ≤ variance w Y := by sorry
