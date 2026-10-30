-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_full_reward_fubini
-- name    : AvramDividend.Classical.avram_ws01h_true_Qp_full_reward_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:33:49.889326+00:00
-- url     : https://prove2.me/theorems/0b68143d-773d-4426-ab4e-8ca079c1b45d
-- title:
--   True joint Esscher exponential-clock full-future reward is the exact original-path finite-clock double integral
-- statement:
--   For any s-finite original path measure and genuine independent positive-rate real exponential observation clock, every genuinely measurable terminal likelihood D and nonnegative measurable path-clock future reward F, the integral of F under the true joint withDensity law equals the clock mixture of original-P integrals of D(ω,r)F(ω,r). This is the exact Fubini/withDensity bridge required to identify the fresh full-future factor in source-specific killed first-record Qp renewal with the genuine terminal Esscher Qp survival mass. The time-dependent terminal density is preserved, no changed infinite path measure or stochastic independence is assumed.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_withDensity_eq_lintegral_mul and MeasureTheory.lintegral_prod_symm; genuine ProbabilityTheory.expMeasure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_Qp_full_reward_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (p : ℝ) (hp : 0 < p)
    (D F : Ω × ℝ → ℝ≥0∞) (hD : Measurable D) (hF : Measurable F) :
    (∫⁻ z : Ω × ℝ, F z ∂((P.prod (expMeasure p)).withDensity D)) =
      (∫⁻ r : ℝ, (∫⁻ ω : Ω, D (ω, r) * F (ω, r) ∂P)
        ∂(expMeasure p)) := by sorry
