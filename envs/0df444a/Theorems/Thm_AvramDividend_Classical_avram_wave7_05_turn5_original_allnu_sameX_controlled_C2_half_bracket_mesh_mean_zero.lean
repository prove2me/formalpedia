-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_controlled_C2_half_bracket_mesh_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_controlled_C2_half_bracket_mesh_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:50:51.884062+00:00
-- url     : https://prove2.me/theorems/3535ad28-3525-4c9e-8e1e-fc49d37e75df
-- title:
--   Canonical original arbitrary-jump controlled Gaussian C2 finite-mesh half-bracket expected zero
-- statement:
--   Exact finite-mesh expectation-zero of Gaussian C2 controlled Taylor residual in the classical half-Hessian, sigma squared over two notation, with actual source X, reserve subtraction, ruin killing, arbitrary X.nu, and an explicit same-source Gaussian pathwise extraction assumption.
-- source:
--   Canonical coefficient and sigma-squared-over-two normalisation of Proved same-source finite-mesh Gaussian centred martingale theorem UUID 1f73818b-86d9-4198-b9b8-43a9852bdfca. Finite moment conditions and same-space Gaussian Y/Levy-Ito pathwise source representation are explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_controlled_C2_half_bracket_mesh_mean_zero
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
    (h : ι → ℝ≥0) :
    let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    (∀ i ∈ S, Integrable (fun ω => G i ω * V i ω) P) →
    (∀ i ∈ S, Integrable (fun ω => (1 / 2 : ℝ) * H i ω) P) →
    (∀ i ∈ S, Integrable (fun ω =>
      ((1 / 2 : ℝ) * H i ω) * (V i ω) ^ 2) P) →
    Integrable (fun ω => Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) ∂P) = 0 := by sorry
