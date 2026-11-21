-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
-- name    : AvramDividend.Classical.avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:40:45.606393+00:00
-- url     : https://prove2.me/theorems/30a3d5a1-157f-4e01-a510-c02914c9afe9
-- title:
--   Original Gaussian stopped physical-grid F0 centring from actual X increments and bounded coefficients
-- statement:
--   For the original zero-jump spectrally negative Lévy process, a finite family of actual stopped centred X increments with deterministic lengths, stopped-filtration predictable Taylor coefficients, bounded stopping times and finite first and second moments admits an integrable finite linear-plus-compensated-quadratic sum Q whose conditional expectation at the original time-0 filtration is zero. This derives the precise Q_j centring/integrability obligations in the genuine original finitecap signed mesh source from independently proved 13c649df and 74caefdd; it cannot assume arbitrary martingale gains or the desired cash budget.
-- source:
--   Exact original stopped Gaussian Lévy physical Ito Taylor finite-grid martingale aggregation, integrable bounded predictables.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite stopped Gaussian Taylor gains are integrable and initially conditionally centred from predictable bounded coefficients and true second moments. -/
theorem AvramDividend.Classical.avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hBound : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (G i))
    (hH : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (H i))
    (M : ι → Ω → ℝ)
    (hM : M = (fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)))
    (hMI : ∀ i ∈ S, Integrable (M i) P)
    (hM2 : ∀ i ∈ S, Integrable (fun ω => (M i ω) ^ 2) P)
    (hGAE : ∀ i ∈ S, AEStronglyMeasurable (G i) P)
    (hHAE : ∀ i ∈ S, AEStronglyMeasurable (H i) P)
    (BG BH : ι → ℝ)
    (hGB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ BG i)
    (hHB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ BH i) :
    let Q : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (G i ω * M i ω +
        (H i ω * M i ω ^ 2 -
          ((h i : ℝ) * X.σ ^ 2) * H i ω))
    Integrable Q P ∧
    condExp (𝓕.rightCont 0) P Q =ᵐ[P]
      (fun _ => (0 : ℝ)) := by sorry
