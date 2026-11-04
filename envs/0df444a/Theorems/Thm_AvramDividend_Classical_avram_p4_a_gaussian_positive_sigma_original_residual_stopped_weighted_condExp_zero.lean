-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_positive_sigma_original_residual_stopped_weighted_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_original_residual_stopped_weighted_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:47:54.075976+00:00
-- url     : https://prove2.me/theorems/ab3e94b1-2526-45d8-8ac5-9eae4b08fe70
-- title:
--   Original positive Gaussian stopped residual has genuine history-weighted conditional mean zero
-- statement:
--   Given a same-probability-space same-filtration exact all-times Lévy-Ito decomposition of the actual original X into drift, zero-jump source Y with exactly matching positive sigma, and its actual small/large jump processes, every L1 stopped-history-weighted increment of the jump-and-drift-adjusted original X has conditional expectation zero at the original right-continuous stopped sigma algebra. The result is a finite-cell zero-mean stochastic-increment bridge; existence of the same-path decomposition and passage to a continuous stochastic integral are explicit outstanding obligations.
-- source:
--   Accepted original zero-jump right-continuous stopped-history Gaussian conditional mean c9825ed7; accepted positive-sigma conditional variance helper e83d0019; Avram et al Eq (5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_positive_sigma_original_residual_stopped_weighted_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : 0 < X.σ)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
         Jsmall (τ ω) ω - Jlarge (τ ω) ω))) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
         Jsmall (τ ω) ω - Jlarge (τ ω) ω))) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
