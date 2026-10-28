-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_exp_mean_antitone_in_h_of_psi_le_q
-- name    : AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_h_of_psi_le_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:11:40.172559+00:00
-- url     : https://prove2.me/theorems/c7ddd2b1-e9b0-4381-89c0-a6879d007a1e
-- title:
--   Expected discounted Lévy increments decrease with horizon above cumulant
-- statement:
--   For a discount at or above the Lévy cumulant, the expected discounted future exponential decreases with the deterministic horizon.
-- source:
--   Both means equal exp(h(ψ(θ)−q)); their comparison follows from the sign of ψ(θ)−q and the ordering of the horizons.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_discounted_increment_laplace
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_discounted_exp_mean_antitone_in_h_of_psi_le_q
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h₁ h₂ : ℝ≥0) (θ q : ℝ) (hθ : 0 ≤ θ) (hle : h₁ ≤ h₂) (hψ : X.ψ θ ≤ q) :
    (∫ ω, Real.exp (-(q * (h₂ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₂) ω - X.X (τ ω) ω)) ∂P) ≤
      ∫ ω, Real.exp (-(q * (h₁ : ℝ))) *
        Real.exp (θ * (X.X (τ ω + h₁) ω - X.X (τ ω) ω)) ∂P := by sorry
