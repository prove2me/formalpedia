-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_first_record_survival_iff_height_bound
-- name    : AvramDividend.Classical.avram_wave3_01_first_record_survival_iff_height_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T12:35:51.152989+00:00
-- url     : https://prove2.me/theorems/0b08ab70-9773-4d31-af46-34e4b37efd0c
-- title:
--   Actual first-record survival is exactly a bound on the maximum reflected drawdown height
-- statement:
--   For a finite genuine first upward passage u of a spectrally negative Lévy process, survival before strict reflected drawdown ruin at positive barrier a is exactly equivalent to the maximum of the actual reflected process on [0,u] being at most a. The proof uses the Proved strict prefix-survival theorem, zero drawdown at a record, and attained upper-semicontinuous compact maximum. It enables the Proved pure infinite-variation atomlessness theorem to control the barrier-parameter continuity of the true killed first-record discount.
-- source:
--   Exact Proved firstUpcrossing_before_barrierRuin_iff_prefix_survival 9a4b2916, firstUpcrossing_runningSup_sub_path_eq_zero 9243feef, reflectedSup_upperSemicontinuousOn_Icc 8cec706c; future pure-jump C1 bridge cd61d678.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_first_record_survival_iff_height_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω) :
    (u : ℝ≥0∞) < barrierRuinTime X a ω ↔
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) ≤ a := by sorry
