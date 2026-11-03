-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:10:33.589536+00:00
-- url     : https://prove2.me/theorems/67171c09-4bab-41b9-86ea-2f0de5dd4faf
-- title:
--   Original arbitrary-jump finite stop Gaussian C2 Hessian half-bracket compensated mesh meanzero
-- statement:
--   For the original arbitrary-jump levy X with a same-filtration Gaussian component Y and exact source decomposition, a finite family of genuine bounded stopping times yields integrable centred Hessian-weighted Gaussian quadratic increments. Each compensated cell has exactly coefficient X.sigma squared divided by two, and the finite stopped mesh has zero expectation. Hessian predictability and L1 moments are automatic from source coefficients and uniform bounds.
-- source:
--   Uses Proved original stopped Hessian measurability UUID 41b798ce-dc51-4499-a4c7-50320ffae570, Mathlib Integrable.of_bound, and newly authored exact source Hessian half-bracket one-cell identity UUID 8118980c-11ec-4f29-8188-1cf22d362f7a (must become Proved for direct proof).

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero
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
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BH : ι → ℝ)
    (hBH : ∀ i ∈ S, 0 ≤ BH i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ BH i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c
    let Q : ι → Ω → ℝ := fun i ω =>
      (1 / 2 : ℝ) * (((1 : ℝ) * V i ω) * (H i ω * V i ω)) -
        (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω
    Integrable (fun ω => ∑ i ∈ S, Q i ω) P ∧
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) = 0 := by sorry
