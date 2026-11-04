-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_bounded_bilinear_L2_isometry
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:28:33.429202+00:00
-- url     : https://prove2.me/theorems/22ba7fb1-a0d1-464f-b8d5-4ab011ceb15c
-- title:
--   Original Gaussian two-weight stopped L2 simple-cell isometry from almost-sure same-source Levy-Ito extraction
-- statement:
--   For actual original jump-bearing Levy X, original right-continuous bounded stop and bounded measurable stopped-history weights G,H, conditional on a single a.s. all-times source decomposition with zero-jump Y, both true weighted X-minus-jumps residual stochastic cells are MemLp 2 and their cross integral is E[GH] h sigma(X)^2. Includes sigma=0; no invented Brownian, pathwise bracket, or simple-integral completion.
-- source:
--   Accepted original source zero-jump bounded predictable bilinear L2 covariance d7cbcb91, pinned MemLp.congr and integral_congr_ae; Avram Eq (5.11).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_L2_covariance
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_ae_original_bounded_bilinear_L2_isometry
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
    MemLp (fun ω => G ω * M ω) 2 P ∧
    MemLp (fun ω => H ω * M ω) 2 P ∧
    (∫ ω, (G ω * M ω) * (H ω * M ω) ∂P) =
      (∫ ω, G ω * H ω ∂P) * ((h : ℝ) * X.σ ^ 2) := by sorry
