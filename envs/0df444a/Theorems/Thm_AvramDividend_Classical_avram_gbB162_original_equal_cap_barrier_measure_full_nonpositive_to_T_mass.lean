-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
-- name    : AvramDividend.Classical.avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:21:07.969946+00:00
-- url     : https://prove2.me/theorems/0a41e763-340b-432f-a6f6-c1702f01b6cb
-- title:
--   Actual original equal-cap barrier Stieltjes dividendMeasure through a physical horizon equals cumulative dividends
-- statement:
--   For the original equal-cap reflected Lévy dividend strategy, the genuine Stieltjes dividendMeasure of the entire physical interval (-∞,T] equals ENNReal.ofReal of the cumulative dividend regulator D(T). The path is zero on negative times, monotone and continuous; pinned Stieltjes measure_Iic gives the exact identity. This makes the original barrier measure finite on every finite nonnegative horizon, helping remove the finite-cash assumption from the short Gaussian direct counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_barrier_full_continuity
open MeasureTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB162_original_equal_cap_barrier_measure_full_nonpositive_to_T_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c : ℝ) (ω : Ω) (T : ℝ≥0) :
    dividendMeasure (barrierStrategy X c c) ω
      (Iic (T : ℝ)) =
    ENNReal.ofReal (barrierStrategy X c c T ω) := by sorry
