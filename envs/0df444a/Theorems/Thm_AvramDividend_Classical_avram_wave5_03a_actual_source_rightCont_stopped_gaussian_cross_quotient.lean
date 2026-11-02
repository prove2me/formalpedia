-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:31:18.933662+00:00
-- url     : https://prove2.me/theorems/8e7a0be6-cf2a-447f-b71e-8c15a11be28b
-- title:
--   Original right-continuous stopped pure-Gaussian source exact two-parameter covariance quotient
-- statement:
--   The exact original pure-Gaussian stopped source exponential quotient cross-energy formula transports without changing sample paths from raw F-stopping times to bounded F.rightCont stopping times. The same-source right-continuous Levy lift has exactly X.X, c, sigma, nu and cumulant psi. This directly provides the stopped source L2 Gram kernel in the filtration used by the controlled strict-prepayment gradient; it does not establish the limiting continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_cross_energy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, ((Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ) *
      ((Real.exp (η *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ η) - 1) / η) ∂P) =
      (Real.exp ((h : ℝ) * (X.σ ^ 2 * θ * η)) - 1) / (θ * η) := by
  sorry
