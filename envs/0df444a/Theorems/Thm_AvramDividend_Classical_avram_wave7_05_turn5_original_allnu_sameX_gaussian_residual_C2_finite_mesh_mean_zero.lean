-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:34:00.470563+00:00
-- url     : https://prove2.me/theorems/1f73818b-86d9-4198-b9b8-43a9852bdfca
-- title:
--   Original arbitrary-jump same-X finite stopped mesh Gaussian C2 residual has exact integrable zero expectation
-- statement:
--   On the exact original spectrally negative Levy X with arbitrary jump measure, the same sample space, probability, filtration and controlled reserve, a finite family of genuine original stopping times has an integrable sum of centred stopped Gaussian C2 residuals and its expectation is exactly zero, conditional on an explicit same-X Levy-Ito Gaussian Y representation and the individual true-source L1 hypotheses.
-- source:
--   Finite-index linearity of the accepted original same-X single stopped Gaussian C2 zero-mean theorem aee12d86-a135-427e-b805-5a211974458a. Retains arbitrary X.nu, true ruin and reserve subtraction, sigma squared coefficient, and explicit unproved same-source Gaussian residual pathwise representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_sameX_gaussian_residual_C2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
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
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (hHsource : ∀ i ∈ S, H i = fun ω => (1 / 2 : ℝ) * (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω)
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c)) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c) ^ 2) P) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * V i ω +
        (H i ω * V i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by sorry
