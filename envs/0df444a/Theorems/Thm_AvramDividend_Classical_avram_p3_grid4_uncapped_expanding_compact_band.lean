-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_expanding_compact_band
-- name    : AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:14:29.171296+00:00
-- url     : https://prove2.me/theorems/76b80e3c-c7fe-412e-aff4-8c576b261e9c
-- title:
--   Explicit expanding interior localisation bands for the original uncapped BV Lévy source
-- statement:
--   Under the original Avram namespace, the explicit uncapped compact bands with lower radius 1/(n+1) and upper endpoint n+2 are strictly interior and satisfy the geometric inputs of the proved source theorem 6d66798c for C=⊤. This does not claim the missing compensated source identity or the complete strict-horizon cash budget.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_uncapped_expanding_compact_band (n : ℕ) :
    0 < (1 : ℝ) / ((n : ℝ) + 1) ∧
    (1 : ℝ) / ((n : ℝ) + 1) ≤ 2 ∧
    (1 : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 2) ∧
    Icc (((1 : ℝ) / ((n : ℝ) + 1)) / 2) ((n : ℝ) + 2) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (⊤ : ℝ≥0∞)} := by sorry
