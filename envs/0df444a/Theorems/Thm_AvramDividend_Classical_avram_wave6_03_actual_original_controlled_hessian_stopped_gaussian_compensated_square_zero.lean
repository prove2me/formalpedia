-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_original_controlled_hessian_stopped_gaussian_compensated_square_zero
-- name    : AvramDividend.Classical.avram_wave6_03_actual_original_controlled_hessian_stopped_gaussian_compensated_square_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:34:09.153798+00:00
-- url     : https://prove2.me/theorems/ed5c933c-bd3e-4cf7-b182-ea01939fc683
-- title:
--   Genuine stopped controlled pre-dividend Hessian cancels the compensated Gaussian quadratic cell in expectation
-- statement:
--   For the original same-path zero-jump spectrally negative Levy source, admissible dividend strategy and C2 capped test, the actual pre-dividend reserve left-limit Hessian stopped at an original right-continuous bounded stopping time is the genuinely predictable coefficient H in the Gaussian quadratic compensator: H*((X_(tau+h)-X_tau-hc)^2-h sigma^2) is integrable and its expectation equals zero. Explicit L1 assumptions on the stopped Hessian and its weighted true-square product guard against the Bochner integral convention for nonintegrable functions. The formula works at sigma=0; it is a finite stopped Gaussian Ito second-order cell, not a general-jump continuous martingale bracket or complete Ito formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_actual_original_controlled_hessian_stopped_gaussian_compensated_square_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0)
    (hHI : Integrable (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) P)
    (hWeightedInt : Integrable (fun ω =>
      (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))
    Integrable (fun ω => H ω *
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 -
        (h : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, H ω * ((X.X (τ ω + h) ω - X.X (τ ω) ω -
        (h : ℝ) * X.c) ^ 2 - (h : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  sorry
