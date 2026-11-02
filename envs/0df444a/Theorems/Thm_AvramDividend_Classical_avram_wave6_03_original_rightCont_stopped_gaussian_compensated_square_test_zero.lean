-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:10:40.793825+00:00
-- url     : https://prove2.me/theorems/e54533f1-d0de-4e1b-8071-48c98d5f3e78
-- title:
--   Original stopped Gaussian compensated square has zero mean against integrable predictable history tests
-- statement:
--   For the actual original spectrally negative Levy process with zero jump measure, a bounded stopping time of its right-continuous filtration, and an integrable stopped-history test weight H whose product with the squared centered future increment is integrable, the genuine stopped quadratic residual (Delta X-h c)^2-h sigma^2 is integrable after multiplication by H and has exactly zero expectation. This converts the Proved same-source predictable quadratic energy identity to the compensated-square martingale-test form required for finite-grid quadratic variation, with arbitrary sigma including zero, no Brownian copy and no unproved bracket assertion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_weighted_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H)
    (hHIntegrable : Integrable H P)
    (hWeightedIntegrable : Integrable (fun ω => H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => H ω * ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, H ω * ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  sorry
