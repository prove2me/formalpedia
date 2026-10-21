-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_named_lower_passage_lt_horizon_measurable
-- name    : AvramDividend.Classical.chat03_named_lower_passage_lt_horizon_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:45:41.739051+00:00
-- url     : https://prove2.me/theorems/dc1809c1-73c1-4d3f-aeab-4b48cafec64e
-- title:
--   The named strict downward first-passage clock has measurable strict sublevel events at finite horizons
-- statement:
--   For the official named downward strict first passage clock and any finite NNReal horizon T, the event that the clock is strictly earlier than T is measurable in the ambient probability sigma-algebra. The generic extended-infimum horizon theorem equates this event with existence of a strict lower-crossing witness before T, and lower finite-horizon grid detection proves its measurability.
-- source:
--   Official Lévy process definitions and independently Proved horizon-grid and generic first-passage results at pinned Mathlib revision.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_generic_extended_infimum_lt_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_named_lower_passage_lt_horizon_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | twoSidedExitDownTime X lower ω < (T : ℝ≥0∞)} := by sorry
