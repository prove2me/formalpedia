-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_stopped_finite_taylor_compensated_expectation_zero
-- name    : AvramDividend.Classical.avram_wave7_05_original_gaussian_stopped_finite_taylor_compensated_expectation_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:51:06.852199+00:00
-- url     : https://prove2.me/theorems/f10c152e-a810-4f21-93c3-ec2b0b1fa133
-- title:
--   Actual-source finite stopped Gaussian gradient and compensated Hessian sum has expectation zero
-- statement:
--   For the original source Lévy process X on Ω under P and its right-continuous stopped filtration, assuming X.ν=0, the finite sum of predictable stopped Gaussian gradient increments plus compensated quadratic Hessian cells is integrable and has expectation zero. All cells use X.X_(τ+h_i)-X.X_τ-h_i c with exact compensation h_i σ²; σ may vanish. This converts the existing remote-proved finite-family conditional expectation into a real expectation identity for simple Gaussian Itô sums. The general-jump continuous martingale remains separate.
-- source:
--   Original-source W7-05 corollary of Proved 01f8f1b2-f954-4558-9538-dbc7a383ba00 and integral_condExp, same Ω/P/filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_original_gaussian_stopped_finite_taylor_compensated_expectation_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hH : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω =>
      G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω =>
      H i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * Y i ω +
        (H i ω * Y i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
