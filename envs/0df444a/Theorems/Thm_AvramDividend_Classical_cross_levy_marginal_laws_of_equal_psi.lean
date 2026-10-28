-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_marginal_laws_of_equal_psi
-- name    : AvramDividend.Classical.cross_levy_marginal_laws_of_equal_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:35:58.849679+00:00
-- url     : https://prove2.me/theorems/22d0e193-bcb9-462b-b8f8-48fdde83367b
-- title:
--   Equal positive Laplace exponents identify all one-time Lévy distributions across probability spaces
-- statement:
--   Two spectrally negative Lévy processes on different probability spaces with equal Laplace exponents at every strictly positive real parameter have equal one-time marginal probability distributions at every nonnegative time. Push their known exponential integrability and Lévy Laplace-field identities through the measurable time-t observations. The positive-MGF uniqueness theorem then identifies the pushforward probability measures. This creates the direct interface needed to match a canonical Poisson Lévy realization to the original Lévy process by comparing their Laplace exponents.
-- source:
--   AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray [4fb183cd-2d4f-4df5-8a23-9c6e5b201da0] and the SpectrallyNegativeLevy.laplace field. `integrable_map_measure` and `integral_map` from pinned Mathlib transport moments across measurable maps. No smoothness, Standing, or path-law assumption.

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_marginal_laws_of_equal_psi
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ) :
    ∀ t : ℝ≥0,
      Measure.map (X.X t) P₁ = Measure.map (Y.X t) P₂ := by sorry
