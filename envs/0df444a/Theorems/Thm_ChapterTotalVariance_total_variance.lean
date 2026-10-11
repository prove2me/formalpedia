-- Prove2me | Theorems.Thm_ChapterTotalVariance_total_variance
-- name    : ChapterTotalVariance.total_variance
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:26:17.846992+00:00
-- url     : https://prove2.me/theorems/b55ce575-97a3-4684-bc68-4e7f447ff7aa
-- title:
--   `ChapterTotalVariance.total_variance` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : variance w Y = within w X Y + between w X Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.total_variance` [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : variance w Y = within w X Y + between w X Y
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.total_variance`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.total_variance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.total_variance [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    variance w Y = within w X Y + between w X Y := by sorry
