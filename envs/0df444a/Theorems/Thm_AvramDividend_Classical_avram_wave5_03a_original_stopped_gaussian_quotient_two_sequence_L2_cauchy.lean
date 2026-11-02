-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_stopped_gaussian_quotient_two_sequence_L2_cauchy
-- name    : AvramDividend.Classical.avram_wave5_03a_original_stopped_gaussian_quotient_two_sequence_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:04:17.439275+00:00
-- url     : https://prove2.me/theorems/6181bbe4-dc22-4b59-8ac2-dc14275c859a
-- title:
--   Original Gaussian stopped exponential quotients have L2 Cauchy cross-distance for all positive null sequences
-- statement:
--   For the actual source spectrally negative Levy process with zero jump measure, any bounded stopping time in its original filtration, and any two sequences of strictly positive exponential parameters tending to zero, the squared L2 distance between their stopped same-path compensated source exponential quotients converges to zero. This is a genuinely two-parameter source Cauchy criterion derived from the exact stopped source covariance kernel and Gaussian exponential secant calculus; it does not presuppose Brownian representation or stochastic Ito integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_L2_distance_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_original_stopped_gaussian_quotient_two_sequence_L2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (Z (θ n) ω - Z (η n) ω) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  sorry
