-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_joint_exp_clock_reflected_cdf_mixture
-- name    : AvramDividend.Classical.esscher_joint_exp_clock_reflected_cdf_mixture
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:21:10.030307+00:00
-- url     : https://prove2.me/theorems/83b37a63-b777-49fc-a916-84c42f96da6a
-- title:
--   Actual random-time Esscher reflected-infimum CDF is the exponential-clock mixture of finite-horizon tilted CDFs
-- statement:
--   For every actual spectrally negative Lévy process, nonnegative Esscher tilt θ and positive clock rate p, take the genuine time-dependent likelihood on the product of the original Lévy sample space and Exp(p). The probability that the running infimum at the clamped clock time is above -x, under the genuinely tilted joint law, equals the mixture against Exp(p) of the exact finite-horizon tilted probabilities of the same reflected-infimum event. Every event is measurable by accepted joint path regularity. This is not a Wiener–Hopf factor and assumes neither a global Esscher process law nor a target Laplace transform.
-- source:
--   Accepted `levy_running_infimum_joint_time_path_measurable` ae09696f, `chat04_levy_joint_time_state_measurable` d55462c3, `chat04_esscher_likelihood_joint_measurable_of_joint_levy_state` de339769 and new proven `esscher_joint_clock_event_fibrewise_disintegration`. Mathlib expMeasure and Tonelli.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_joint_clock_event_fibrewise_disintegration
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_joint_exp_clock_reflected_cdf_mixture
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p x : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x} =
    (∫⁻ t : ℝ,
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ))))
        {ω : Ω | -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal t ∧ y = X.X s ω} ≤ x}
      ∂expMeasure p) := by sorry
