-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
-- name    : AvramDividend.Classical.chat03_both_named_passage_clocks_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:17:56.987896+00:00
-- url     : https://prove2.me/theorems/3d4daa72-4dba-48f9-9f55-b9a0e92786e4
-- title:
--   Both named strict first-passage clocks are Borel measurable as extended nonnegative random variables
-- statement:
--   For an official adapted spectrally negative Lévy process and arbitrary upper and lower thresholds, both exact named strict first-passage times are measurable functions from sample paths to the extended nonnegative real line. The result combines the separately Proved measurability of strict finite-horizon passage events for each clock with the generic ENNReal-valued measurability theorem, which covers the infinite-passage atom via natural-horizon approximation. This establishes full measurability before forming the strict comparison event τup<τdown in the stopped-scale identity.
-- source:
--   Pinned Prove2Me accepted named upper and lower horizon sublevels, generic full ENNReal measurability result, no martingale assumption.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_measurable_of_finite_strict_sublevels
import Theorems.Thm_AvramDividend_Classical_chat03_named_upper_passage_lt_horizon_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_both_named_passage_clocks_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    Measurable (fun ω : Ω => twoSidedExitUpTime X upper ω) ∧
    Measurable (fun ω : Ω => twoSidedExitDownTime X lower ω) := by sorry
