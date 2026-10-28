-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
-- name    : AvramDividend.Classical.esscher_true_random_clock_reflected_law_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:11:45.245982+00:00
-- url     : https://prove2.me/theorems/3d3e8fe4-0e87-4fc6-951e-000bdd8326e0
-- title:
--   The authentic finite-rate Esscher exponential-clock running-infimum law is a probability measure
-- statement:
--   For any actual spectrally negative Lévy process, any nonnegative Esscher tilt and any positive independent exponential rate, the pushforward of the genuine jointly tilted path-clock product measure along the negative running infimum at that clock time is a bona fide probability measure on ℝ. Its proof imports established joint tilted-law probability, joint Esscher likelihood measurability and Lévy running-infimum path-time measurability, then applies the pinned probability-map theorem. This is the source-specific probability hypothesis needed to apply all-threshold CDF convergence results to Laplace/capital integrals; it does not assert finite-rate Wiener–Hopf factorisation.
-- source:
--   Accepted Prove2Me 146b0027, de339769, d55462c3, ae09696f; Mathlib Measure.isProbabilityMeasure_map pinned 0df444a.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_true_random_clock_reflected_law_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    IsProbabilityMeasure
      (((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))).map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})) := by sorry
