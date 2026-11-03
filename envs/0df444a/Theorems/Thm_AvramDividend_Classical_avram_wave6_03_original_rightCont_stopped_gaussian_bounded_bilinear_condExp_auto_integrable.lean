-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:47:32.154213+00:00
-- url     : https://prove2.me/theorems/a52309b8-5be6-406f-befd-5921676b3177
-- title:
--   Automatic L1 and exact conditional Gaussian covariance of two bounded stopped weights
-- statement:
--   For the authentic zero-jump Lévy source on the original Omega with the right-continuous stopped history, arbitrary sigma including zero, two bounded predictable historical weights produce L2 stochastic cells. Their cross-product is automatically genuinely L1 by Hölder and its conditional stopped Gaussian covariance is h sigma squared GH. Unlike the preceding general conditional covariance, this theorem discharges product integrability from concrete L2 assumptions, ready for source predictable simple stochastic integration. It does not claim a continuous Gaussian residual for a jump-bearing X.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGglobal : Measurable G) (hHglobal : Measurable H)
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hGbound : ∀ ω, |G ω| ≤ BG)
    (hHbound : ∀ ω, |H ω| ≤ BH) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P ∧
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by
  sorry
