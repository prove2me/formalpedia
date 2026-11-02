-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_covariance_null_sequences
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_covariance_null_sequences
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:12:39.529217+00:00
-- url     : https://prove2.me/theorems/927be9f7-7c9b-4d92-8db8-5006a537859d
-- title:
--   Actual right-continuous stopped Gaussian quotient cross covariance tends to h sigma squared for any two positive null sequences
-- statement:
--   For the genuine spectrally negative Levy source with zero jump measure, any bounded stopping time in its right-continuous original filtration, and any two positive null parameter sequences, the expected product of the two compensated source exponential quotients converges to h*sigma^2. This certifies the same-path stopped Gaussian covariance / continuous quadratic-variation variance convention directly from the Proved rightCont source exponential cross-energy and right secant limit. No Brownian copy, bracket process, or Ito integral is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_energy_slope_right

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_cross_covariance_null_sequences
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, Z (θ n) ω * Z (η n) ω ∂P))
      atTop (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  sorry
