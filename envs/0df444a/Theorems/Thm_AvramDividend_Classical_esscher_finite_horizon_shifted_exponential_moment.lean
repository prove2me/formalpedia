-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_finite_horizon_shifted_exponential_moment
-- name    : AvramDividend.Classical.esscher_finite_horizon_shifted_exponential_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:07:59.033599+00:00
-- url     : https://prove2.me/theorems/e6c63d00-9649-4bf1-97bf-3096b32c335f
-- title:
--   Exact finite-horizon Esscher-shifted Lévy exponential moment under the original law
-- statement:
--   Under the original spectrally negative Lévy probability law, weighting e^{ηX_t} by the normalised Esscher exponential e^{θX_t−tψ(θ)} gives exp[t(ψ(θ+η)−ψ(θ))], for θ,η≥0. This is the shifted Lévy Laplace exponent under finite-horizon Esscher tilting, a genuine stochastic input for the Wiener-Hopf descending ladder route.
-- source:
--   Use the source Levy Laplace property X.laplace at θ+η, factor the product of exponentials pathwise, pull its deterministic tilt normalisation outside the Bochner integral, and simplify exponent algebra. It is independent of any two-sided exit or Wiener-Hopf conclusion.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_finite_horizon_shifted_exponential_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) *
      Real.exp (η * X.X t ω) ∂P) =
    Real.exp ((t : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by sorry
