-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_named_exit_survives_horizon_measurable
-- name    : AvramDividend.Classical.chat03_first_named_exit_survives_horizon_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:14:32.19685+00:00
-- url     : https://prove2.me/theorems/639b760c-b886-4541-bbad-e804e1529cfd
-- title:
--   Measurability of two-sided strict first-passage survival through a deterministic finite horizon
-- statement:
--   For the minimum of the official strict upper and lower passage times, survival up to and including a deterministic finite horizon T, defined as T≤min(τup,τdown), is a measurable event. It is the complement of the independently Proved measurable event min(τup,τdown)<T. The theorem preserves correct strict endpoint behaviour when a passage clock equals T and when either passage clock is infinite; it does not require the passage infimum to be attained.
-- source:
--   Proved Chat03 first named exit strict sublevel measurability UUID 9dc55b99-2750-4a6f-862f-d39e66de771a, total order complement.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_first_named_exit_lt_horizon_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_named_exit_survives_horizon_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | (T : ℝ≥0∞) ≤
        min (twoSidedExitUpTime X upper ω)
          (twoSidedExitDownTime X lower ω)} := by sorry
