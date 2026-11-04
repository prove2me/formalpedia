-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_ae_decomposition_finite_grid_half_drift
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_decomposition_finite_grid_half_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:05:06.478179+00:00
-- url     : https://prove2.me/theorems/06a1c48d-c10c-476a-bc88-b7d655c438e2
-- title:
--   Original Gaussian finite-grid expected half-drift from almost-sure all-time source decomposition
-- statement:
--   For the actual original spectrally negative Levy X and an almost-sure all-times same-source Gaussian/jump decomposition, proves integrability of a finite stopped-history quadratic Gaussian residual sum and exact expected source sigma²/2 drift. This AE interface is appropriate for stochastic processes without arbitrary exceptional-path assumptions. Does not construct the continuous local martingale or Brownian motion, or claim mesh convergence.
-- source:
--   Accepted source zero-jump finite grid aa7f4cc5; accepted strict source original finite grid d53709dd; source Eq 5.11 and pinned integrable.congr, integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_finite_grid_half_drift
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_ae_decomposition_finite_grid_half_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ (u : ℝ≥0),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i : ι, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHstop : ∀ i : ι,
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (R : ι → Ω → ℝ)
    (hR : ∀ i ω, R i ω = X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω -
        (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))
    (hWeightedInt : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (R i ω) ^ 2) P) :
    Integrable (fun ω => ∑ i ∈ S,
      (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2) P ∧
    (∫ ω, ∑ i ∈ S,
      (1 / 2 : ℝ) * H i ω * (R i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (((h i : ℝ) * X.σ ^ 2) / 2) * (∫ ω, H i ω ∂P) := by sorry
