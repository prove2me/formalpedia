-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_lower_stopped_payoff_at_min_clock
-- name    : AvramDividend.Classical.avram_root29_03_lower_stopped_payoff_at_min_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:46:40.073426+00:00
-- url     : https://prove2.me/theorems/6661672f-4857-4c8f-b240-8ab7b16cc923
-- title:
--   Actual lower-first stopped payoff is its value at the minimum exit clock
-- statement:
--   For any genuine original-process lower-before-upper strict passage event, any nonnegative measurable-space measure and any nonnegative payoff depending on the stopping clock and path, the lower-first restricted lintegral evaluated at the minimum of the actual upper/lower exit clocks equals that evaluated at the actual lower exit clock. The integrands are pathwise equal, so no reward measurability or variation assumption is needed. This retains any lower-boundary creeping contribution.
-- source:
--   Pathwise min_eq_right on true lower-first event, integrated with lintegral_congr. Source-specific adapter for the original X stopped two-sided killed q-scale harmonicity; independent of Open be9, BV OST and no-creeping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_lower_stopped_payoff_at_min_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (g : ℝ≥0∞ → Ω → ℝ≥0∞) :
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then
      g (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)) ω
    else 0 ∂μ) =
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then
      g (twoSidedExitDownTime X (-x) ω) ω
    else 0 ∂μ) := by sorry
