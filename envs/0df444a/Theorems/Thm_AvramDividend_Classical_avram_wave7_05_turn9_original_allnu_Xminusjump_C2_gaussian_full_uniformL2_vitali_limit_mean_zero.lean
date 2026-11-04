-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn9_original_allnu_Xminusjump_C2_gaussian_full_uniformL2_vitali_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_gaussian_full_uniformL2_vitali_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:02:26.20363+00:00
-- url     : https://prove2.me/theorems/08994e90-526e-4275-be9b-fd244a776bde
-- title:
--   Original C2 Gaussian controlled finite-mesh uniform L2 Vitali almost-everywhere limit has zero mean
-- statement:
--   Under an exact same-sample-space zero-jump Gaussian component and pathwise Levy-Ito decomposition of the canonical spectrally negative Levy X, every finite stopped C2 Gaussian residual has expectation zero. Replacing a common pointwise integrable envelope by a uniform L2 seminorm bound, Mathlib/Prove2Me uniform integrability and Vitali imply that almost-everywhere mesh convergence to L preserves expectation zero. Integrands are the original stopped dividend-controlled left-reserve gradient and Hessian; the Hessian compensator is exactly sigma squared over two. Original decomposition, a.e. convergence and uniform L2 bound remain explicit hypotheses.
-- source:
--   Proved finite original controlled Gaussian mesh identity UUID 0b4b1222-7d33-4c04-9a59-2de46db5fdd6. Proved L2-to-uniform-integrability helper UUID 6ecde2f8-f759-4772-8894-8a5887983551; previously proved finite-measure Vitali pattern UUID a641544b-c2b0-4f1c-902a-c3ba941f7879.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_C2_gaussian_full_finite_ito_mesh_mean_zero
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_gaussian_full_uniformL2_vitali_limit_mean_zero
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
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n, ∀ i ∈ S n, G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (hHsource : ∀ n, ∀ i ∈ S n, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (BG BH : ℕ → ι → ℝ)
    (hBG : ∀ n, ∀ i ∈ S n, 0 ≤ BG n i)
    (hBH : ∀ n, ∀ i ∈ S n, 0 ≤ BH n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ BG n i)
    (hHbound : ∀ n, ∀ i ∈ S n, ∀ ω, |H n i ω| ≤ BH n i)
    (L : Ω → ℝ) (C₂ : ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      M (τ n i ω + h n i) ω - M (τ n i ω) ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n,
        (G n i ω * V n i ω + (1 / 2 : ℝ) * H n i ω *
          (V n i ω ^ 2 - (h n i : ℝ) * X.σ ^ 2))
    (∀ n, eLpNorm (Q n) (2 : ℝ≥0∞) P ≤ C₂) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    (∫ ω, L ω ∂P) = 0 := by sorry
