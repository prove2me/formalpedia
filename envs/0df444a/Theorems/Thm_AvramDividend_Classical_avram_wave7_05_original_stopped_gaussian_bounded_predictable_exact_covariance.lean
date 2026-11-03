-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_exact_covariance
-- name    : AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bounded_predictable_exact_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:51:40.599206+00:00
-- url     : https://prove2.me/theorems/2b2d29aa-6572-4fc1-9484-7e1b605cd12e
-- title:
--   Bounded original stopped predictable Gaussian gains have automatic L1 and exact covariance
-- statement:
--   For bounded predictable stopped-history weights applied to the literal original X.X Gaussian centred increment, their product is automatically integrable and its expectation is exactly h sigma squared E[GH]. No independent Brownian sample space or nonzero jump residual is assumed; source sigma can vanish.
-- source:
--   W7-05 original-source expectation corollary of Proved a52309b8-5be6-406f-befd-5921676b3177 and pinned integral_condExp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_bounded_bilinear_condExp_auto_integrable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bounded_predictable_exact_covariance
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
      (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by sorry
