-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_stationary_laplace
-- name    : AvramDividend.Classical.levy_bounded_stopping_increment_stationary_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:31:16.030207+00:00
-- url     : https://prove2.me/theorems/09a53fe2-4e8c-4a4c-be28-54274be47f82
-- title:
--   Stationary Laplace transform of a Lévy increment after a bounded stopping time
-- statement:
--   For a bounded stopping time τ, the exponential moment of the future increment X_(τ+h)−X_τ equals that of the deterministic-time increment X_h for every nonnegative Laplace parameter θ. This is the strong Markov stationary-increment Laplace identity and is useful for dividend verification.
-- source:
--   Corollary of the proved bounded-stopping increment Laplace theorem and SpectrallyNegativeLevy.laplace.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.levy_bounded_stopping_increment_stationary_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
      ∫ ω, Real.exp (θ * X.X h ω) ∂P := by sorry
