-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:42:36.343731+00:00
-- url     : https://prove2.me/theorems/9a6959fe-c4cc-44b9-803f-38d448475a7e
-- title:
--   Original physical Poisson clock and mark intensity cast from ENNReal to real product
-- statement:
--   The real rate of the original physical negative-jump Poisson count is the real time horizon multiplied by the real negative-mark intensity, exactly matching the source count-law ENNReal rate equation.
-- source:
--   Pinned Mathlib ENNReal.toReal_mul, coercion from NNReal to ENNReal and real.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Converting the original physical Poisson clock/intensity product gives the real count rate. -/

theorem AvramDividend.Classical.avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117 (t : ℝ≥0) (markRate : ℝ≥0∞) :
    (((t : ℝ≥0∞) * markRate).toReal) =
      (t : ℝ) * markRate.toReal := by sorry
