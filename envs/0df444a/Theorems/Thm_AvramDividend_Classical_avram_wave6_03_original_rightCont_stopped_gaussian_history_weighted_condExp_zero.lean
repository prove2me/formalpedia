-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:53:05.663922+00:00
-- url     : https://prove2.me/theorems/c9825ed7-d9b4-486a-9b4d-e1b7950d2a8c
-- title:
--   Actual stopped-history weighted source Gaussian increment is conditionally zero with true L1 product
-- statement:
--   For the actual spectrally negative Levy source with ν=0, bounded original right-continuous stopping time τ, and an arbitrary τ-history measurable coefficient H such that the genuine product H*(X_(τ+h)-X_τ-hc) is L1, prove its conditional expectation at the original stopped sigma algebra is zero. This strictly strengthens the canonical accepted unconditioned weighted mean-zero theorem and exports the stopped simple-integral martingale difference directly. Use the newly accepted true conditional source mean-zero and Mathlib pull-out. Arbitrary σ including zero; no detached Brownian copy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
