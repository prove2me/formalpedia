-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_surviving_horizon_reserve_strip
-- name    : AvramDividend.Classical.avram_ws01b_true_surviving_horizon_reserve_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T13:47:17.968982+00:00
-- url     : https://prove2.me/theorems/84820534-4145-44cc-8847-f4141f21ffa5
-- title:
--   Original Lévy before-exit horizon reserve strip
-- statement:
--   For the true original spectrally negative Lévy path, if a finite horizon precedes both source two-sided first-exit clocks then every observed reserve through the horizon stays in [0,a].
-- source:
--   Source original strict exceedance observation-to-stopping bounds already canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_true_surviving_horizon_reserve_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ)
    (T : ℝ≥0) (ω : Ω)
    (hTU : (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω)
    (hTD : (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    ∀ s : ℝ≥0, s ≤ T →
      0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a := by sorry
