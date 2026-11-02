-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
-- name    : AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:06:47.7185+00:00
-- url     : https://prove2.me/theorems/f3b5d1bb-efa2-4d74-b5b7-813d47bc858c
-- title:
--   Actual stopped pure-Gaussian source exponential difference quotients have exact cross L2 kernel
-- statement:
--   For the actual original-filtration source process with ν=0, arbitrary bounded stopping clock and nonnegative parameters θ,η, the L2 cross moment of the centred exponential divided by θ and by η equals (exp(hσ² θη)-1)/(θη). This provides the two-parameter same-path covariance kernel needed to construct the Gaussian martingale derivative as an L2 limit. The theorem is an exact finite-parameter result and does not claim the limit exists or that an independent Brownian copy represents X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η) := by
  sorry
