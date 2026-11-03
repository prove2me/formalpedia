-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_bracket_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_bracket_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:35:54.070815+00:00
-- url     : https://prove2.me/theorems/31284e5e-6df4-4c33-a3f4-6c944d60637f
-- title:
--   Original arbitrary-jump same-X finite stopped Gaussian C2 bilinear bracket exact zero expectation
-- statement:
--   For the canonical controlled original Levy process with arbitrary jumps, under explicit same-space Gaussian component representation, a finite family of true original stopping-time source gradient and Hessian coefficients has integrable centred bilinear Gaussian quadratic bracket with mean zero. The variance correction uses the exact sigma squared of X.
-- source:
--   Finite expected bracket aggregation of accepted source-specific conditional bracket 437c730f-7650-41cd-a535-cdcb3520c9a8. Integrates each original stopped conditional expectation and sums finite integrable cells. Existence of the original same-X Gaussian component remains an explicit separate source decomposition hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_exact_conditional_bracket

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_bracket_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (hGHInt : ∀ i ∈ S, Integrable (fun ω => G i ω * H i ω) P)
    (hWeightedInt : ∀ i ∈ S, Integrable (fun ω =>
      (G i ω * H i ω) *
        (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c) ^ 2) P)
    (hFInt : ∀ i ∈ S, Integrable (fun ω =>
      let V := Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
      (G i ω * V) * (H i ω * V) -
        ((h i : ℝ) * X.σ ^ 2) * (G i ω * H i ω)) P) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let F : ι → Ω → ℝ := fun i ω =>
      (G i ω * V i ω) * (H i ω * V i ω) -
        ((h i : ℝ) * X.σ ^ 2) * (G i ω * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
