-- Prove2me | Theorems.Thm_ChapterTotalVariance_variance_nonneg
-- name    : ChapterTotalVariance.variance_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:00.195986+00:00
-- url     : https://prove2.me/theorems/4f8a20dc-d4fc-45c5-95e2-9b6fc5c744c2
-- title:
--   `ChapterTotalVariance.variance_nonneg` (w Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ variance w Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTotalVariance`.
--
--   `ChapterTotalVariance.variance_nonneg` (w Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) : 0 ≤ variance w Y
--
--   Formalization note: Lean 4 identifier `ChapterTotalVariance.variance_nonneg`.

-- Generated from ChapterTotalVariance.lean — theorem ChapterTotalVariance.variance_nonneg
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance



open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

theorem ChapterTotalVariance.variance_nonneg (w Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    0 ≤ variance w Y := by sorry
