-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_stopped_weighted_sigma_variance_exact
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_stopped_weighted_sigma_variance_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:44:53.827563+00:00
-- url     : https://prove2.me/theorems/675ef712-9791-4bca-b268-e15a418bafaa
-- title:
--   Original jump-bearing Lévy actual stopped Gaussian weighted quadratic energy equals sigma squared clock energy
-- statement:
--   Assuming a same-sample-space a.s. all-times Levy-Ito extraction of genuine X into zero-jump Y of matching sigma and original Jsmall/Jlarge, the exact random bounded stopped Gaussian residual weighted L2 energy equals the history-weight energy times h X.sigma². Works sigma zero or positive; no Brownian substitution, no C2 outside interior.
-- source:
--   Proved zerojump original source exact stopped weighted L2 isometry 4294d18f-9e1d-43e0-a67a-c123a1438800; a.s. transport via integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_L2_isometry_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_stopped_weighted_sigma_variance_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hHglobal : Measurable H) :
    let M : Ω → ℝ := fun ω =>
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    (∫ ω, (H ω * M ω) ^ 2 ∂P) =
      (∫ ω, (H ω) ^ 2 ∂P) * ((h : ℝ) * X.σ ^ 2) := by sorry
