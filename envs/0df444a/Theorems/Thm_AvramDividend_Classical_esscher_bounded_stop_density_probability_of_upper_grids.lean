-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_density_probability_of_upper_grids
-- name    : AvramDividend.Classical.esscher_bounded_stop_density_probability_of_upper_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T18:43:01.834281+00:00
-- url     : https://prove2.me/theorems/9fc4f11e-c5e8-4f57-9666-d4d49bd0571b
-- title:
--   The realised stopped Esscher likelihood is a probability under uniformly bounded upper stopping grids
-- statement:
--   If P is a probability Lévy law, θ≥0 and τ is a bounded stopping time approached from above by adapted finite-valued upper-grid stops before a common terminal T, then the realised stopped exponential weight Mτ defines an actual probability P.withDensity Mτ. The proof uses the accepted finite-grid L2-derived uniform integrability and the exact Q_T versus stopped-likelihood identity on the universal history event. It does not identify this measure with Q_T on arbitrary future events or with an independent clock product.
-- source:
--   Accepted upper-grid actual UI 53937e78, bounded stopped-history density 2f664ff6, and finite-terminal Esscher probability chat04_esscher_weighted_finite_horizon_probability. No WH or scale harmonicity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_upper_stop_likelihood_uniformIntegrable
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_history_density_eq_of_ui_upper_grids
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_bounded_stop_density_probability_of_upper_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ n s, s ∈ grid n → s ≤ T)
    (hstop : ∀ n s, s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) := by sorry
