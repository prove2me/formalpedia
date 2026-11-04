-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn9_original_allnu_Xminusjump_C2_gaussian_full_ae_dct_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_gaussian_full_ae_dct_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:49:15.123319+00:00
-- url     : https://prove2.me/theorems/30e78e3a-c585-42d4-83e4-32c2e086e1c9
-- title:
--   Original X-minus-jumps controlled C2 Gaussian stopped full finite-mesh dominated a.e. limit has zero expectation
-- statement:
--   For the exact original SpectrallyNegativeLevy P 𝓕 and dividend-controlled C2 gradient/Hessian evaluated at the original left-limit reserve and ruin time, a finite bounded right-continuous stopping mesh gives a Gaussian residual Q_n on M=X.X-tX.c-Jsmall-Jlarge. Under an explicit same-space zero-jump Y decomposition, an integrable envelope g dominating every Q_n a.e. and almost-everywhere convergence to L imply E[L]=0. Neither Integrable L nor L1 convergence of the meshes is assumed; original decomposition, envelope and a.e. limit remain explicit hypotheses.
-- source:
--   Remotely Proved original source C2 finite stopped Gaussian Ito mesh meanzero UUID 0b4b1222-7d33-4c04-9a59-2de46db5fdd6 and pinned MeasureTheory.tendsto_integral_of_dominated_convergence.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_C2_gaussian_full_finite_ito_mesh_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_gaussian_full_ae_dct_limit_mean_zero
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
    (L g : Ω → ℝ) (hgI : Integrable g P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      M (τ n i ω + h n i) ω - M (τ n i ω) ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n,
        (G n i ω * V n i ω + (1 / 2 : ℝ) * H n i ω *
          (V n i ω ^ 2 - (h n i : ℝ) * X.σ ^ 2))
    (∀ n, ∀ᵐ ω ∂P, ‖Q n ω‖ ≤ g ω) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    (∫ ω, L ω ∂P) = 0 := by sorry
