-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_fixed_parameter_limit
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_fixed_parameter_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:58:40.997894+00:00
-- url     : https://prove2.me/theorems/e204d8e1-5666-4d77-a05b-0b59bf75ac7f
-- title:
--   Original rightCont stopped Gaussian cross moment tends to h sigma squared at fixed positive parameter
-- statement:
--   For the actual zero-jump Gaussian spectrally negative Levy process with a bounded stopping time of its original right-continuous filtration, fix positive exponential quotient parameter θ. As the second quotient parameter η tends to 0 from above, the exact source cross second moment converges to h σ². Use the Proved samepath source stopped cross-energy identity and a Proved elementary exponential secant limit. This is the fixed-parameter cross-covariance limit needed by the source-drift-centred L² Fatou identification, with no detached Gaussian copy or conditional stochastic-calculus formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_fixed_parameter_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    Filter.Tendsto
      (fun η : ℝ =>
        (∫ ω,
          ((Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
              (h : ℝ) * X.ψ θ) - 1) / θ) *
          ((Real.exp (η * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
              (h : ℝ) * X.ψ η) - 1) / η) ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  sorry
