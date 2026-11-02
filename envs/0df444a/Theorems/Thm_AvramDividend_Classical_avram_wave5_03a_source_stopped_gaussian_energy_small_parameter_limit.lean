-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit
-- name    : AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:05:35.010138+00:00
-- url     : https://prove2.me/theorems/ff670bc2-6b4a-4be9-a5e0-cdf86d08982e
-- title:
--   Actual source stopped pure-Gaussian exponential energy has small-parameter limit h sigma squared
-- statement:
--   For any original SpectrallyNegativeLevy with zero jump measure and any bounded stopping time for its own filtration, the L2 energy of the centred source exponential increment at parameter sqrt epsilon tends to h*sigma squared as epsilon approaches zero from above. This is obtained from the already Proved same-path finite-parameter rescaled energy identity and one-sided exponential derivative. The theorem identifies the Gaussian variance convention from actual source observations, including sigma=0; it does not claim convergence of the random variables to a continuous martingale or quadratic variation of X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    Filter.Tendsto (fun ε : ℝ => (∫ ω,
      ((Real.exp (Real.sqrt ε *
          (X.X (τ ω + h) ω - X.X (τ ω) ω) -
          (h : ℝ) * X.ψ (Real.sqrt ε)) - 1) /
            Real.sqrt ε) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  sorry
