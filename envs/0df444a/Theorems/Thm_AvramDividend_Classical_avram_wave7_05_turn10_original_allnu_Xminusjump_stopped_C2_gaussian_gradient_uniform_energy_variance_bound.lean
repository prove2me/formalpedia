-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:48:47.071927+00:00
-- url     : https://prove2.me/theorems/5ebd38c2-6fd5-47e7-84c0-f7b5ce5e726a
-- title:
--   Original source Gaussian C2 stopped derivative one-cell uniform quadratic energy variance bound
-- statement:
--   For original spectrally negative Lévy X, the same-space zero-jump Gaussian component Y and original reserve with dividend subtraction, the predictable stopped discounted C2 derivative gains at bounded stopping times have second moment at most T sigma^2 E whenever the localised derivative energy is uniformly bounded by E and each Gaussian step is at most T. This is a source-specific second moment localisation criterion used to derive the uniform L2 hypothesis for the Vitali Gaussian Itô limit.
-- source:
--   Canonical AvramDividend.Classical riskProcess/ruinTime, proven Wave7 source-specific stopped Gaussian L2 isometry, exact original same-space bridge explicitly stated; no unrelated Brownian space.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (B : ℕ → ℝ≥0) (hbounded : ∀ n ω, τ n ω ≤ B n)
    (h : ℕ → ℝ≥0) (hStep : ∀ n, h n ≤ T)
    (G : ℕ → Ω → ℝ)
    (hGsource : ∀ n, G n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (BG : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n)
    (hGbound : ∀ n ω, |G n ω| ≤ BG n)
    (E : ℝ) (hE : 0 ≤ E)
    (hEnergy : ∀ n, (∫ ω, G n ω * G n ω ∂P) ≤ E) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → Ω → ℝ := fun n ω =>
      M (τ n ω + h n) ω - M (τ n ω) ω
    ∀ n, (∫ ω, (G n ω * V n ω) ^ 2 ∂P) ≤
      (T : ℝ) * X.σ ^ 2 * E := by sorry
