-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_C2_source_taylor_expected_jump_mesh
-- name    : AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_C2_source_taylor_expected_jump_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:54:24.813999+00:00
-- url     : https://prove2.me/theorems/6fc20120-0a2e-4a16-a00c-12315326077a
-- title:
--   Original arbitrary-jump controlled C2 stopped Taylor finite-mesh expected jump identity via Gaussian cancellation
-- statement:
--   On exactly the canonical source X with arbitrary Lévy jump measure, the finite-mesh expectation of the ruin-discounted controlled C2 Taylor increments equals the expectation of the explicit jump correction sum, because the stopped Gaussian C2 half-bracket has zero expectation, conditional on the same-source Gaussian residual representation and all stated L1 hypotheses.
-- source:
--   Combines two Proved independent original-source theorems: finite mesh exact pathwise Gaussian/jump Taylor split a5b511f4-876f-4da2-aade-198c6fb1747f and same-X finite mesh centred Gaussian expectation zero 1f73818b-86d9-4198-b9b8-43a9852bdfca. Keeps hSourceDecomp, true controlled reserve, true ruin and exact σ²/2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_samepath_gaussian_jump_C2_finite_mesh_split
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_C2_source_taylor_expected_jump_mesh
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
    let A : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let J : ι → Ω → ℝ := fun i ω =>
      (Jsmall (τ i ω + h i) ω - Jsmall (τ i ω) ω) +
      (Jlarge (τ i ω + h i) ω - Jlarge (τ i ω) ω)
    let Full : Ω → ℝ := fun ω => Finset.sum S (fun i =>
      G i ω * A i ω +
        (1 / 2 : ℝ) * H i ω * (A i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))
    let Jump : Ω → ℝ := fun ω => Finset.sum S (fun i =>
      G i ω * J i ω + H i ω * V i ω * J i ω +
        (1 / 2 : ℝ) * H i ω * J i ω ^ 2)
    (∀ i ∈ S, Integrable (fun ω => G i ω * V i ω) P) →
    (∀ i ∈ S, Integrable (fun ω => (1 / 2 : ℝ) * H i ω) P) →
    (∀ i ∈ S, Integrable (fun ω =>
      ((1 / 2 : ℝ) * H i ω) * V i ω ^ 2) P) →
    Integrable Jump P →
    Integrable Full P ∧ (∫ ω, Full ω ∂P) = (∫ ω, Jump ω ∂P) := by sorry
