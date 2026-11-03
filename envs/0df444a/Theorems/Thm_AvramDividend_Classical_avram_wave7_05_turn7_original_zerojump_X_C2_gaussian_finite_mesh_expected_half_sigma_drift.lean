-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_finite_mesh_expected_half_sigma_drift
-- name    : AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_finite_mesh_expected_half_sigma_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:28:07.348802+00:00
-- url     : https://prove2.me/theorems/99c8c568-fb3b-4a9e-9076-1b7a08e2bcfc
-- title:
--   Direct original zero-jump X controlled C2 Gaussian finite stopped mesh Ito expected drift sigma squared over two
-- statement:
--   On the exact original spectrally negative Levy source X with zero jump measure, all finite stopped C2 derivative and Hessian weighted Gaussian Ito increments based on X.X are integrable, with sum expectation equal to sigma squared over two times the finite duration-weighted expected original-control Hessians. Original Omega, P, filtration, x+X.X-rightLimit D and ruin stopping are preserved; there is no independent model.
-- source:
--   Specialises the remotely Proved original-source all-nu C2 Gaussian finite mesh expected-drift identity to Y=X, Jsmall=Jlarge=0 with algebraic source decomposition.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_source_C2_gaussian_finite_mesh_ito_expected_drift

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_finite_mesh_expected_half_sigma_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c
    Integrable (fun ω => ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S,
      (G i ω * V i ω + (1 / 2 : ℝ) * H i ω * V i ω ^ 2) ∂P) =
      ∑ i ∈ S, ((((h i : ℝ) * X.σ ^ 2) / 2) *
        (∫ ω, H i ω ∂P)) := by sorry
