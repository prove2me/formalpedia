-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:48:48.337266+00:00
-- url     : https://prove2.me/theorems/1bda0221-07ff-4f80-86a8-d170658e4d92
-- title:
--   Original controlled C2 Hessian finite stopped Gaussian half-bracket on X-minus-jumps is centred
-- statement:
--   On exactly the canonical SpectrallyNegativeLevy X, its right-continuous filtration, original dividend reserve and ruin gate, stopped Hessian H from C2 test w has a finite half quadratic-variation compensated sum of Gaussian residual increments M=X.X-tX.c-Jsmall-Jlarge with integral zero and integrability. A same-space zero-jump Levy Y and original source decomposition are explicit hypotheses.
-- source:
--   Algebraic source-decomposition transfer of the remotely Proved original-source C2 Gaussian finite half bracket compensator theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
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
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    let Q : ι → Ω → ℝ := fun i ω =>
      (1 / 2 : ℝ) * (((1 : ℝ) * V i ω) * (H i ω * V i ω)) -
        (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω
    Integrable (fun ω => ∑ i ∈ S, Q i ω) P ∧
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) = 0 := by sorry
