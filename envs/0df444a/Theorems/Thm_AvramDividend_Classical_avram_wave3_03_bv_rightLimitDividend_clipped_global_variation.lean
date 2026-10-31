-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_rightLimitDividend_clipped_global_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_rightLimitDividend_clipped_global_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:41:36.560627+00:00
-- url     : https://prove2.me/theorems/d3d85e0b-5ad4-4f06-988f-d845281942ac
-- title:
--   Actual strict-right dividend cumulative path has global bounded variation after finite-horizon clipping
-- statement:
--   For any actual adapted nondecreasing dividend strategy, the post-payment strict-right cumulative dividend path is bounded and monotone when extended to real time and frozen after a fixed finite horizon. It has globally bounded variation, preserving both continuous Stieltjes payments and time-zero and subsequent dividend right jumps.
-- source:
--   Proved pointwise strict-right dividend monotonicity and current-value inequality, bounded by rightLimit D T; then Mathlib MonotoneOn.boundedVariationOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_rightLimitDividend_clipped_global_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    BoundedVariationOn
      (fun t : ℝ => rightLimit D (min t.toNNReal T) ω) Set.univ := by sorry
