-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitTimes_eq_zero_iff_bilateral_crossings_at_threshold
-- name    : AvramDividend.Classical.twoSidedExitTimes_eq_zero_iff_bilateral_crossings_at_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:09:54.958803+00:00
-- url     : https://prove2.me/theorems/6b3de729-036c-4781-a8e1-e98bd1e1dd4f
-- title:
--   Pathwise bilateral regularity at an arbitrary threshold
-- statement:
--   Both strict first-passage clocks equal zero at a threshold if and only if the path visits both sides of that threshold arbitrarily soon.
-- source:
--   Two independently remote-verified pathwise first-passage equivalences.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitTimes_eq_zero_iff_bilateral_crossings_at_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    (twoSidedExitDownTime X b ω = 0 ∧ twoSidedExitUpTime X b ω = 0) ↔
      ((∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) ∧
       (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω)) := by sorry
