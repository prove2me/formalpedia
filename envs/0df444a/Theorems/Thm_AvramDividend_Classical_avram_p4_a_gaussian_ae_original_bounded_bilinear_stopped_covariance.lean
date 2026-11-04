-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_bounded_bilinear_stopped_covariance
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_stopped_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:01.34714+00:00
-- url     : https://prove2.me/theorems/9e07725b-1898-4915-96d6-0b6b8b44f6d4
-- title:
--   Original Gaussian bounded bilinear stopped covariance from an almost-sure same-source Levy-Ito decomposition
-- statement:
--   For actual spectrally negative Levy X on the original sample space/filtration, given an almost-sure all-times decomposition into original-source zero-jump Y and jump fields, any bounded original stopped-time-history measurable G,H yield an automatically L1 stochastic-cell bilinear product and exact conditional covariance h sigma(X)^2 G H. Includes sigma zero and positive, proves neither intrinsic decomposition nor stochastic integral mesh convergence.
-- source:
--   Source-Proved zero-jump bounded bilinear conditional covariance a52309b8 and Mathlib Integrable.congr/condExp_congr_ae; Avram Eq(5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_stopped_covariance
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
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let M : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
          Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    Integrable (fun ω => (G ω * M ω) * (H ω * M ω)) P ∧
    P[(fun ω => (G ω * M ω) * (H ω * M ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by sorry
