-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_C2_finite_residual_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_C2_finite_residual_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:52:15.36334+00:00
-- url     : https://prove2.me/theorems/74d9394c-db18-4483-ae8f-1113b0019c6f
-- title:
--   Canonical X minus compensated source jump components has centred stopped C2 Gaussian finite Ito mesh residual
-- statement:
--   Define directly on the canonical spectrally negative Lévy sample space the source continuous residual M_t = X.X_t - t X.c - Jsmall_t - Jlarge_t. When an explicit same-space Lévy-Itô decomposition by pure Gaussian Y with the same sigma is supplied, the stopped finite C2 Gaussian Ito residual using M increments has integrable expectation exactly zero and the sigma squared/2 correction. Original control D, ruin time, stopped derivative integrands and filtration are preserved. This theorem does not construct Y or Jsmall/Jlarge from X.
-- source:
--   Exact original-source finite Gaussian C2 stopped Ito residual UUID f32d179f-6212-406a-a0ff-855cad98395c Proved. Source decomposition pathwise identifies M increments with centred Y.X stopped increments; finite mean zero follows. Directly bridges original X minus its compensator and jump terms to the Gaussian stochastic identity.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_full_finite_ito_mesh_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_C2_finite_residual_mean_zero
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
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    Integrable (fun ω => ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω *
        (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω *
        (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) ∂P) = 0 := by sorry
