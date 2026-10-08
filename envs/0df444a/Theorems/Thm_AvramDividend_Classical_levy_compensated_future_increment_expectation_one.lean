-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_compensated_future_increment_expectation_one
-- name    : AvramDividend.Classical.levy_compensated_future_increment_expectation_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:23:07.131191+00:00
-- url     : https://prove2.me/theorems/46c4e22d-4f9a-414e-9f66-86e9f39566af
-- title:
--   Normalised future Lévy increment has unit expectation
-- statement:
--   For s≤t and θ≥0, the compensated exponential of the future Lévy increment X_t−X_s, normalised by the stationary time difference t−s and Laplace exponent ψ(θ), has expectation one. IdentDistrib of increments with X_{t−s} transfers the previously established compensated exponential expectation through a measurable exponential function.
-- source:
--   Direct consequence of SpectrallyNegativeLevy.stationaryIncrements and ProbabilityTheory.IdentDistrib.comp.integral_eq, combined with AvramDividend.Classical.levy_compensated_exponential_expectation_one. This is one prerequisite for an exponential Lévy martingale and subsequent generator-to-martingale arguments for Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_compensated_future_increment_expectation_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ) ∂P) = 1 := by sorry
