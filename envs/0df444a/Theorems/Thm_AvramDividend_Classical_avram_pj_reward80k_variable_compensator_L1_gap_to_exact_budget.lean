-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80k_variable_compensator_L1_gap_to_exact_budget
-- name    : AvramDividend.Classical.avram_pj_reward80k_variable_compensator_L1_gap_to_exact_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T08:05:49.896382+00:00
-- url     : https://prove2.me/theorems/5e0188f8-cf25-48b5-995b-210cd60af5e5
-- title:
--   Changing spatial bands with vanishing signed positive HJB gap and nonpositive expected compensated drift imply exact cash upper bound
-- statement:
--   When each requested positive error tolerance permits a potentially different integrable compensated generator H of nonpositive mean, and the positive original stopped payoff gap has mean bounded by the tolerance, the original exact stopped reward expectation is bounded by the initial HJB value. Covers epsilon-dependent spatial and Lévy cutoffs without fixing an incompatible band.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80k_variable_compensator_L1_gap_to_exact_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (G : Ω → ℝ)
    (hGI : Integrable G P)
    (hSource : ∀ ε : ℝ, 0 < ε →
      ∃ H : Ω → ℝ,
        Integrable H P ∧
        (∫ ω, H ω ∂P) ≤ 0 ∧
        (∫ ω, max (0 : ℝ) (G ω - (a + H ω)) ∂P) ≤ ε) :
    (∫ ω, G ω ∂P) ≤ a := by sorry
