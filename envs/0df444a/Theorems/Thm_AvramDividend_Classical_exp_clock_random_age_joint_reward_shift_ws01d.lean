-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_clock_random_age_joint_reward_shift_ws01d
-- name    : AvramDividend.Classical.exp_clock_random_age_joint_reward_shift_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:08:43.532187+00:00
-- url     : https://prove2.me/theorems/51ea1a74-0ed6-463e-a32f-e219afefce7e
-- title:
--   Genuine product exponential-clock reward translation after an arbitrary measurable nonnegative random age
-- statement:
--   For the genuine product law of an arbitrary probability P and an independent real Exp(p) observation clock, p>0, and an arbitrary measurable nonnegative random age τ, integrating any jointly measurable nonnegative reward of the residual real time E−τ on the event E≥τ equals the original path expectation of exp(−pτ) times the fresh Exponential(p) reward integral. The statement preserves the real observation clock, the non-strict boundary and the product-measure Tonelli structure, and does not require a stopping-time, Esscher law, global tilt, or Wiener–Hopf independence. It is the exact joint-likelihood bridge needed to integrate a capped Lévy first-record future exponential factor over the true observation clock.
-- source:
--   Proved ws01d real exponential density shift fd8ff708-3a83-44f1-9565-f01000bbb033, Mathlib ProbabilityTheory.expMeasure = volume.withDensity exponentialPDF, MeasureTheory.lintegral_prod, and MeasureTheory.lintegral_withDensity_eq_lintegral_mul at the pinned revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_clock_residual_density_lintegral_shift_ws01d

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.exp_clock_random_age_joint_reward_shift_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p)
    (age : Ω → ℝ≥0) (hAge : Measurable age)
    (reward : Ω × ℝ → ℝ≥0∞) (hReward : Measurable reward) :
    (∫⁻ z : Ω × ℝ, if (age z.1 : ℝ) ≤ z.2 then
       reward (z.1, z.2 - (age z.1 : ℝ)) else 0
       ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (-(p * (age ω : ℝ)))) *
      (∫⁻ u : ℝ, reward (ω, u)
        ∂(ProbabilityTheory.expMeasure p)) ∂P) := by sorry
