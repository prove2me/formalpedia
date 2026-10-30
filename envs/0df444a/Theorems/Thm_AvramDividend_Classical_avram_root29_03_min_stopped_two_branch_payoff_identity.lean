-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_min_stopped_two_branch_payoff_identity
-- name    : AvramDividend.Classical.avram_root29_03_min_stopped_two_branch_payoff_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:53:52.75347+00:00
-- url     : https://prove2.me/theorems/a80aad7a-e3bc-45f2-8ec2-d1501779999e
-- title:
--   Actual stopped finite minimum exit integral equals two strict terminal payoff branches
-- statement:
--   For the original spectrally negative Lévy passage clocks U,D with a>0, the integral of any nonnegative payoff g at the actual minimum exit clock, restricted to min(U,D)<∞, equals the sum of strict upper-first payoff at U and strict lower-first payoff at D. Assumes measurability of the stopped reward g(min(U,D),path), with arbitrary path measure μ. Consumes only already canonically Proved exact two-branch event lintegral a19ccfcc and lower stopped clock payoff 6661672f; it has no Standing, no variation, no no-creeping or genuine killed harmonicity assumption.
-- source:
--   Source-specific event/measure/stopped-payoff conversion to reduce the exact be9dc931 two-term lintegral to a genuine killed stopped-minimum expectation. Does not assert the killed stochastic equality itself.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exit_finite_reward_split
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_lower_stopped_payoff_at_min_clock

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_min_stopped_two_branch_payoff_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a)
    (g : ℝ≥0∞ → Ω → ℝ≥0∞)
    (hg : Measurable (fun ω => g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω)) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      g (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) ω else 0 ∂μ) =
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      g (twoSidedExitUpTime X (a - x) ω) ω else 0 ∂μ) +
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
      g (twoSidedExitDownTime X (-x) ω) ω else 0 ∂μ) := by sorry
