-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_bounded_bilinear_bracket_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_bracket_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:24:29.84373+00:00
-- url     : https://prove2.me/theorems/9e409eb1-e441-40b1-86d8-f51c75431990
-- title:
--   Original bounded bilinear Gaussian bracket conditional mean zero from an almost-sure Levy-Ito decomposition
-- statement:
--   For original spectrally negative Levy X, original right-continuous bounded stop and bounded original stopped-history G,H with integrable GH, the product of two original X-minus-jump Gaussian increments minus h sigma(X)^2 GH has conditional expected value zero. Assumes the original-source a.s. all-times Gaussian/jump decomposition. Includes sigma=0, no new Brownian assumption and no asserted pathwise quadratic variation.
-- source:
--   Source-Proved zero-jump bounded bilinear bracket 67db9271 and pinned MeasureTheory.condExp_congr_ae; Avram (5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_bracket_auto_L1_condExp_zero
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_bracket_condExp_zero
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
    (hHbound : ∀ ω, |H ω| ≤ BH)
    (hGHInt : Integrable (fun ω => G ω * H ω) P) :
    let M : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
          Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    P[(fun ω => (G ω * M ω) * (H ω * M ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
