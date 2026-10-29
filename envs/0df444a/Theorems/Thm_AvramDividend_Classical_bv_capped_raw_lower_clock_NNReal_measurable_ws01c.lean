-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_capped_raw_lower_clock_NNReal_measurable_ws01c
-- name    : AvramDividend.Classical.bv_capped_raw_lower_clock_NNReal_measurable_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:12:13.005706+00:00
-- url     : https://prove2.me/theorems/4bfef2e3-db2c-4d63-b73e-35108cefdc80
-- title:
--   The capped strict lower passage clock has a measurable finite nonnegative value
-- statement:
--   The actual strict lower first-passage ENNReal clock is measurable. Capping at a deterministic finite T and applying ENNReal.toNNReal yields a measurable finite NNReal random clock, without modifying the original filtration.
-- source:
--   Causal resubmission of failed publication job 993a919b-0a0a-4d96-a8f9-3d137d9187e1, whose sole terminal error was unavailable import bv_raw_lower_clock_measurable_ws01c. That exact prerequisite is now independently Proved, UUID 9d4c0774-269b-43c5-b08f-9e736e21a8f1. Original mathematical statement and preamble preserved. Complete 20-line proof is work/avram_ws01c_capped_raw_clock_meas_solution_direct.lean.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_bv_raw_lower_clock_measurable_ws01c

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_capped_raw_lower_clock_NNReal_measurable_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (lower : ℝ) (T : ℝ≥0) :
    Measurable (fun ω : Ω =>
      (twoSidedExitDownTime X lower ω ⊓ (T : ℝ≥0∞)).toNNReal) := by sorry
