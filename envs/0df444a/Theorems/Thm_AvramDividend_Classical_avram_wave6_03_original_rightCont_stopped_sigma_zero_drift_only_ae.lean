-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_sigma_zero_drift_only_ae
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_sigma_zero_drift_only_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:51:00.315039+00:00
-- url     : https://prove2.me/theorems/c6d977c7-4265-4362-9bee-7e02aa1d6386
-- title:
--   Exact original stopped pure-drift increment almost surely when source nu and sigma both vanish
-- statement:
--   For a genuine spectrally negative Levy source with vanishing jump measure and sigma zero, every bounded stopping time of its original right-continuous filtration has its actual same-path future increment equal to the drift h*c almost surely. Use the proved exact original stopped Gaussian L2 variance, the square-integral zero criterion, and nonnegativity. This discharges the degenerate Gaussian endpoint without requiring sigma positive or constructing a Brownian copy. It is not a theorem about arbitrary-jump sources.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_sigma_zero_drift_only_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : X.σ = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) :
    ∀ᵐ ω ∂P,
      X.X (τ ω + h) ω - X.X (τ ω) ω = (h : ℝ) * X.c := by
  sorry
