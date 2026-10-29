-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_raw_lower_clock_measurable_ws01c
-- name    : AvramDividend.Classical.bv_raw_lower_clock_measurable_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:58:45.304976+00:00
-- url     : https://prove2.me/theorems/9d4c0774-269b-43c5-b08f-9e736e21a8f1
-- title:
--   The actual raw strict lower first-passage clock is measurable
-- statement:
--   Measurability of the actual raw strict lower first-passage ENNReal clock follows from Proved measurable finite strict-horizon sublevels. No original-filtration stopping-time claim is introduced.
-- source:
--   Causal repair of terminal failed job bf2f87f1-abbe-4789-9faf-765c3994bfb6. The old preamble lacked open scoped NNReal, so ℝ≥0 in the Filtration binder was parsed as an order expression, causing LE and 0 mΩ errors. The new preamble adds only NNReal/ENNReal scopes and preserves the exact statement. Proof work/avram_ws01c_raw_clock_meas_solution_repair_20261028.lean.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_measurable_of_finite_strict_sublevels

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_raw_lower_clock_measurable_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (lower : ℝ) :
    Measurable (twoSidedExitDownTime X lower) := by sorry
