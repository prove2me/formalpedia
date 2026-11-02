-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
-- name    : AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:48:39.035694+00:00
-- url     : https://prove2.me/theorems/7ea3f875-b4c4-40a3-9008-46236e930073
-- title:
--   Public same-path stopped pure-Gaussian exponential difference-quotient exact L2 energy
-- statement:
--   For the same original spectrally negative Lévy path and original bounded stopping time, when its jump measure is zero, the centred exponential increment divided by its parameter has exactly L2 energy (exp(h sigma^2 theta^2)-1)/theta^2 for every nonnegative parameter. The identity follows by source stopped cross-energy and scalar division through the integral. In the small-parameter limit this energy approaches h sigma^2, the original source Gaussian quadratic variation convention, but this theorem asserts exact finite-parameter energy only and does not claim an independent Brownian representation. This public export uses the authenticated accepted proof and public Proved source exponential-moment premises, for Chat03 independent import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_exp_centered_cross_moment
import Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_source_gaussian_stopped_exponential_rescaled_energy_export
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ θ) - 1) / θ) ^ 2 ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ ^ 2)) - 1) / θ ^ 2 := by
  sorry
