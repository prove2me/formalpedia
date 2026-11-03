-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bilinear_exact_expected_covariance
-- name    : AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bilinear_exact_expected_covariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:44:53.896188+00:00
-- url     : https://prove2.me/theorems/fc52cc99-0e05-4517-a47a-0fa5634a3e48
-- title:
--   Exact original-source stopped predictable Gaussian bilinear L2 covariance
-- statement:
--   For the actual original zero-jump Lévy source and its bounded right-continuous stopping time, two stopped-history predictable L2 source gains have covariance h sigma squared times the expected weight product under explicit integrability. This supplies exact stopped source Gaussian isometry with arbitrary sigma including sigma zero, not a replacement for mixed-jump continuous martingale splitting.
-- source:
--   W7-05 corollary of Proved 00bc46b1-17d8-448b-b0c5-e8d50674220f and Mathlib integral_condExp over original stopped history.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_bilinear_condExp_covariance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_bilinear_exact_expected_covariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGH : Integrable (fun ω => G ω * H ω) P)
    (hProductIntegrable : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => (G ω * Y ω) * (H ω * Y ω)) P ∧
      (∫ ω, (G ω * Y ω) * (H ω * Y ω) ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * H ω ∂P) := by sorry
