-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
-- name    : AvramDividend.Classical.avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:57:54.568194+00:00
-- url     : https://prove2.me/theorems/03d633e3-fe2d-4ee7-bbd0-95b604b541c7
-- title:
--   Strict Lévy terminal drawdown/infimum symmetry under the genuine random-terminal Esscher exponential clock
-- statement:
--   On the actual joint path–independent exponential observation-clock law weighted by exp(θ X_e − e ψ(θ)), terminal drawdown and running infimum relative to zero have equal joint probabilities for every strict real threshold, provided the actual random-terminal Esscher likelihood is measurable. Fibrewise, use the proved finite-terminal Esscher strict reversal and canonical zero-start density identity for every positive sampled horizon, and handle zero-length horizons by equality of both strict events. Apply the proved weighted random-clock section transfer and proved joint path-clock strict event measurability. This is true random-terminal Esscher probability symmetry rather than an assumed global tilted Lévy law, but it does not itself claim Wiener–Hopf independence.
-- source:
--   Proved avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal (pending publication), canonical_esscher_density_eq_displacement_density, joint_weighted_clock_section_probability_transfer, levy_random_horizon_strict_events_measurable.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_canonical_esscher_density_eq_displacement_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_weighted_clock_section_probability_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_random_horizon_strict_events_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p a : ℝ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X z.2.toNNReal z.1 - X.X s z.1 < a} =
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ θ))))
      {z : Ω × ℝ | ∃ s : ℝ≥0, s ≤ z.2.toNNReal ∧
        X.X s z.1 - X.X 0 z.1 < a} := by sorry
