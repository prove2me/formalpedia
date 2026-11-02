-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export
-- name    : AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:44:04.635709+00:00
-- url     : https://prove2.me/theorems/238d8077-d591-483d-96a0-d090d9841572
-- title:
--   Public same-source bounded-stopped pure Gaussian exponential cross covariance
-- statement:
--   For any actual SpectrallyNegativeLevy X on its original probability space and filtration, with no jumps (X.ν=0), arbitrary bounded stopping time τ and deterministic future horizon h, the exact cross moment of two centred stochastic exponentials of the source increment is exp(h σ² θη)-1 for nonnegative θ,η. This follows from the already canonically Proved original-process stopping-time cross moment and the exact source Laplace exponent, without a detached Gaussian copy. This is a same-path second-moment input towards the Gaussian L² martingale derivative and quadratic-variation construction, not itself an Ito formula. Public export for independent Chat03 imports using the same public source stopped Lévy moment and zero-jump Laplace exponent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_centered_cross_moment
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_cross_energy_export
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    ∫ ω, (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) *
      (Real.exp (η *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ η) - 1) ∂P =
      Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1 := by
  sorry
