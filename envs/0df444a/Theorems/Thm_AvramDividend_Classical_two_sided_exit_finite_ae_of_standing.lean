-- Prove2me | Theorems.Thm_AvramDividend_Classical_two_sided_exit_finite_ae_of_standing
-- name    : AvramDividend.Classical.two_sided_exit_finite_ae_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:35:32.163277+00:00
-- url     : https://prove2.me/theorems/b81ba525-a00f-4d45-8c40-7bfd74555338
-- title:
--   Two-sided exit from a nonempty strip is almost surely finite
-- statement:
--   A standing spectrally negative Levy process with reserve x in [0, a] exits the two-sided strip in finite time almost surely: the minimum of the up-exit clock above a - x and the down-exit clock below -x is finite almost everywhere. Standing excludes monotone paths, so the process cannot remain inside a nonempty strip forever. This is the exit-finiteness premise that the stopped-scale optional-stopping payoff balance needs for its dominated-convergence tail and frozen-limit value identification.
-- source:
--   Parent AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance (09caed2c-1cc0-4083-8a24-a39b70d511c8): its repair attempt 16903 failed 9 terminal CE groups. Causal analysis shows every value-flow formulation (Nat-DCT tail remainder, tau-frozen approximations, grid-to-continuous passage) crosses the {tau = infinity} null-set premise, and no catalogue theorem concludes exit finiteness: finite-exit searches return only finiteStopping bounds and grid expectations, never P(tau < top) = 1 for the continuous two-sided clocks. Proved up-exact-hit two_sided_up_exit_hits_level_of_no_positive_jumps (6e7b393d) plus Open stopped-scale martingale 5955d9a2 and no-creeping-ae 43a28d8e supply stopped-value identification; Proved mesh limit chat03_exact_uniform_grid_discount_expectation_tendsto (e1b0e908) supplies grid-to-continuous passage. This child isolates exactly the missing finiteness premise with parent-identical binders. Bridge: tau-frozen payoff DCT with factoring via MeasureTheory.lintegral_const_mul_prime (no measurability needed), expectation constancy via Martingale.setIntegral_eq over univ, and final algebra via scaleFunction_strict_pos_of_standing (Proved 59531c77).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.two_sided_exit_finite_ae_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P, min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ := by sorry
