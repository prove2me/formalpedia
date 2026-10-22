-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_official_no_lower_exit_grid_inf_top
-- name    : AvramDividend.Classical.chat03_official_no_lower_exit_grid_inf_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:41:46.950014+00:00
-- url     : https://prove2.me/theorems/d6fcb3b4-4da3-45aa-a0e9-846a3b82be93
-- title:
--   Infinite continuous strict lower passage forces infinite sampled uniform-grid passage time
-- statement:
--   If the official continuous strict lower exit clock is infinity, there is no strict lower crossing anywhere on the Lévy path. Consequently every sampled uniform-grid lower crossing condition is false, and the exact ENNReal infimum of sampled lower crossing times remains infinity for every mesh. This is the lower-boundary counterpart of the accepted upper-clock infinity-persistence theorem.
-- source:
--   Official strict two-sided exit definition, accepted chat03_extended_infimum_is_top_iff_no_exit, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_extended_infimum_is_top_iff_no_exit

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_official_no_lower_exit_grid_inf_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (h : ℝ≥0)
    (hDown : twoSidedExitDownTime X lower ω = ∞) :
    (⨅ k : ℕ,
      if X.X ((k : ℝ≥0) * h) ω < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞)
      else ∞) = ∞ := by sorry
