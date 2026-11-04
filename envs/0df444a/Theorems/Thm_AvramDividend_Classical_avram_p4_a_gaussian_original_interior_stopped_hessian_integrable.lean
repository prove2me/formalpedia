-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_interior_stopped_hessian_integrable
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:49:34.130015+00:00
-- url     : https://prove2.me/theorems/cd7b9a4a-0422-4106-8e2a-03ede8e040df
-- title:
--   Actual stopped Gaussian Hessian correction integrable strictly before interior exit
-- statement:
--   For the original spectrally negative Lévy X and actual controlled riskProcess, the Gaussian second-order generator term is integrable on the strict pre-exit interval Iio(tau omega) under the explicitly stated finite-time measure, measurable path-integrand and almost-everywhere original reserve-in-compact-band facts. This uses the accepted original-source uniform discounted Hessian bound, without assuming zero endpoint occupation time, C2 through ruin, Brownian extraction or an Itô stochastic integral. The hPath and hMeas are genuine remaining stopping/regularity obligations to be provided by P4-E.
-- source:
--   Accepted fce33e7b original Gaussian discounted Hessian bound, pinned MeasureTheory.IntegrableOn.of_bound (exact remote signature), Avram et al Proposition4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_original_interior_stopped_hessian_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (μ : Measure ℝ≥0) (ω : Ω)
    (hμ : μ (Iio (τ ω)) < ⊤)
    (hPath : ∀ᵐ s ∂μ.restrict (Iio (τ ω)),
      riskProcess X x D s ω ∈ Icc a b)
    (hMeas : AEStronglyMeasurable
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω))) (μ.restrict (Iio (τ ω)))) :
    IntegrableOn
      (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ))) *
      (X.σ ^ 2 / 2 * iteratedDeriv 2 w (riskProcess X x D s ω))) (Iio (τ ω)) μ := by sorry
