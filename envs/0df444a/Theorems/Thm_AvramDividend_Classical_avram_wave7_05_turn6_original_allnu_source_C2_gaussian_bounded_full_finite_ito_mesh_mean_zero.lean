-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_finite_ito_mesh_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_finite_ito_mesh_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:36:11.555117+00:00
-- url     : https://prove2.me/theorems/f32d179f-6212-406a-a0ff-855cad98395c
-- title:
--   Original all-jump same-filtration controlled C2 Gaussian finite stopped Ito mesh centred with sigma squared half bracket
-- statement:
--   On the canonical arbitrary-jump X and its dividend-controlled reserve, a same-space zero-jump Gaussian component Y with matched sigma and explicit pathwise decomposition gives fully integrable bounded stopped C2 finite-mesh Ito Gaussian residuals. The sum of gradient times centred Gaussian increment plus half Hessian times compensated square has exact zero expectation. Stopped predictability and moments are supplied by the one-cell source theorem.
-- source:
--   Proved or pending one-cell bounded full Gaussian source C2 residual UUID to be confirmed from authoring job 07da8629-cb02-4001-a6f4-cec762e09bc4; finite-sum Bochner integral. Original source extraction and true Ito mesh convergence remain hypotheses.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_onecell_residual_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_finite_ito_mesh_mean_zero
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
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BG BH : ι → ℝ)
    (hBG : ∀ i ∈ S, 0 ≤ BG i) (hBH : ∀ i ∈ S, 0 ≤ BH i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ BG i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ BH i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c
    let Q : ι → Ω → ℝ := fun i ω =>
      G i ω * V i ω + (1 / 2 : ℝ) * H i ω *
        (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)
    Integrable (fun ω => ∑ i ∈ S, Q i ω) P ∧
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) = 0 := by sorry
