-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn9_original_allnu_Xminusjump_C2_hessian_half_bracket_uniformL2_vitali_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_hessian_half_bracket_uniformL2_vitali_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:04:35.225848+00:00
-- url     : https://prove2.me/theorems/8ef494b4-b6d4-43ca-a5fb-144cabc881b1
-- title:
--   Original X controlled C2 Hessian half-bracket uniform L2 Vitali limit meanzero
-- statement:
--   For canonical SpectrallyNegativeLevy X, with exact same Ω/P/filtration zero-jump Gaussian Y and explicit original-source decomposition, stopped C² Hessian half-bracket finite residuals have mean zero. Their almost-everywhere mesh limit remains expectation zero under a uniform L² seminorm bound, using verified uniform-integrability and Vitali. The source is the dividend-controlled reserve left limit and its actual ruin time, and coefficient is exactly σ²/2.
-- source:
--   Proved original full Levy X minus jumps Hessian half-bracket finite compensation UUID 1bda0221-07ff-4f80-86a8-d170658e4d92, plus Proved L2-to-uniform-integrability UUID 6ecde2f8-f759-4772-8894-8a5887983551.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_hessian_half_bracket_uniformL2_vitali_limit_mean_zero
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
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (H : ℕ → ι → Ω → ℝ)
    (hHsource : ∀ n, ∀ i ∈ S n, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (BH : ℕ → ι → ℝ)
    (hBH : ∀ n, ∀ i ∈ S n, 0 ≤ BH n i)
    (hHbound : ∀ n, ∀ i ∈ S n, ∀ ω, |H n i ω| ≤ BH n i)
    (Z : Ω → ℝ) (C₂ : ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      M (τ n i ω + h n i) ω - M (τ n i ω) ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n,
        ((1 / 2 : ℝ) * (((1 : ℝ) * V n i ω) *
          (H n i ω * V n i ω)) -
          (((h n i : ℝ) * X.σ ^ 2) / 2) * H n i ω)
    (∀ n, eLpNorm (Q n) (2 : ℝ≥0∞) P ≤ C₂) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (Z ω))) →
    (∫ ω, Z ω ∂P) = 0 := by sorry
