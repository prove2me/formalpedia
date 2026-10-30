-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_finite_reward_split
-- name    : AvramDividend.Classical.avram_root29_03_exit_finite_reward_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:41:54.178136+00:00
-- url     : https://prove2.me/theorems/a19ccfcc-c0a4-473f-bea9-869c5c0f24b8
-- title:
--   Finite original two-sided exit reward splits into strict upper and lower passage branches
-- statement:
--   For the actual upper/lower strict passage clocks of a spectrally negative Lévy process with a positive upper barrier, the nonnegative payoff integrated over paths where at least one exit clock is finite equals the sum of its strictly upper-first and strictly lower-first integrals under an arbitrary measure. The two branches are disjoint, finite simultaneous passage is excluded by the already Proved original-clock no-finite-ties result. No Standing, variation, no-creeping or stochastic killed harmonicity is assumed.
-- source:
--   Source-exact event-disjoint integration adapter from canonically Proved original-path exit clock partition 0002b530 and strict upper passage measurability. It preserves the lower-creeping contribution while preparing two-branch stopped-scale optional stopping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_clock_partition_of_finite
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_exit_finite_reward_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (f : Ω → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < ⊤ ∨
        twoSidedExitDownTime X (-x) ω < ⊤ then f ω else 0 ∂μ) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then f ω else 0 ∂μ) +
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then f ω else 0 ∂μ) := by sorry
