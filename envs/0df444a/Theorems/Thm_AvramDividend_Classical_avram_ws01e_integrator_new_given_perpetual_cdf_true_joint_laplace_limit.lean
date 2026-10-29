-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_given_perpetual_cdf_true_joint_laplace_limit
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_given_perpetual_cdf_true_joint_laplace_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:58:45.957347+00:00
-- url     : https://prove2.me/theorems/1c4ecff1-e645-4600-a071-473188d515f6
-- title:
--   Genuine tilted random-clock Laplace convergence to a specified perpetual CDF probability
-- statement:
--   For any actual spectrally negative Lévy process and θ≥0, if a specific genuine probability ν supported on [0,∞) has the canonical tilted infinite-horizon survival CDF, then every positive exponential-rate sequence tending to zero has genuine realised-time Esscher negative-infimum pushforward Laplace transforms converging to the Laplace transform of this same ν. This strengthens existential statements by preserving the supplied canonical ν and assumes no Wiener-Hopf independence or descending factor.
-- source:
--   Accepted exact CDF convergence for a supplied ν 58668a61-8546-404d-bc77-56b91bd22993; probability CDF weighted-limit 0bf634fd-5a21-4348-b978-ad0ae7b83c60; supported probability weighted-CDF/ENNReal Laplace identity; actual joint pushforward probability 3d3e8fe4 and nonnegative support 4e6aabf8. The original accepted 858282df result has only an existential ν; this is the reusable precise-witness strengthening required for scalar integration.

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
import Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_integrator_new_given_perpetual_cdf_true_joint_laplace_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (ν : Measure ℝ) (hνP : IsProbabilityMeasure ν)
    (hν0 : ν (Iio (0 : ℝ)) = 0)
    (hνCDF : ∀ x : ℝ, ν (Iic x) =
      (⨅ t : ℝ≥0, ENNReal.ofReal
        (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∀ β : ℝ, 0 < β →
      Tendsto (fun n : ℕ =>
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂
          (Measure.map (fun z : Ω × ℝ =>
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1})
            ((P.prod (expMeasure (p n))).withDensity
              (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
                (θ * X.X (Real.toNNReal z.2) z.1 -
                  (Real.toNNReal z.2 : ℝ) * X.ψ θ)))))))
        atTop (nhds (∫⁻ z : ℝ,
          ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) := by sorry
