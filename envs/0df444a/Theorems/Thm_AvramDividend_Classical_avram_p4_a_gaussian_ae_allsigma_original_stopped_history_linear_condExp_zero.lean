-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_allsigma_original_stopped_history_linear_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_allsigma_original_stopped_history_linear_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:33:24.225825+00:00
-- url     : https://prove2.me/theorems/bd4c4950-7bc5-4f6f-b528-9f174d1bc2e9
-- title:
--   All-sigma original Levy stopped-history Gaussian linear conditional zero with almost-sure extractor
-- statement:
--   A zero-jump Gaussian source Y on the original probability space and an almost-sure all-times extraction of original X imply that the original-X Gaussian stopped residual weighted by any integrable stopped-history random variable has conditional expectation zero. This holds for X.sigma=0 and X.sigma>0, including pure-jump unbounded variation; no auxiliary Brownian path is introduced.
-- source:
--   Source Proved c9825ed7-d9b4-486a-9b4d-e1b7950d2a8c; transport by a.e. decomposition and conditional-expectation congruence. This removes superfluous positive sigma and pointwise equality assumptions from older positive-sigma helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_allsigma_original_stopped_history_linear_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ (u : ℝ≥0),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
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
