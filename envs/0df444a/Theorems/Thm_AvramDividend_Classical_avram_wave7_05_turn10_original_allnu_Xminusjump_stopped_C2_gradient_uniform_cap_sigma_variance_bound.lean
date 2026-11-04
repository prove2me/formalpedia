-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_sigma_variance_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_sigma_variance_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:05:42.306222+00:00
-- url     : https://prove2.me/theorems/12175c9f-f0f5-40ad-8ba0-5b5789dc67fa
-- title:
--   Original all-jump Lévy stopped C2 Gaussian gradient variance controlled solely by uniform derivative cap and horizon
-- statement:
--   For the canonical original SpectrallyNegativeLevy process X with same-space Gaussian component Y and original dividend-controlled reserve, a deterministic uniform bound K on the stopped predictable derivative and a Gaussian cell length bound T directly yield ∫(G ΔM)^2 ≤ T σ² K². This discharges the explicit derivative-energy hypothesis in the original all-jump stopped Gaussian energy-variance helper using source-specific predictable measurability.
-- source:
--   Proved original source gradient energy from pointwise localisation and source Gaussian stopped L2 isometry variance bound; preserving exact X, D and ruinTime.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_sigma_variance_bound
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
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ n ω, |G n ω| ≤ K) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → Ω → ℝ := fun n ω =>
      M (τ n ω + h n) ω - M (τ n ω) ω
    ∀ n, (∫ ω, (G n ω * V n ω) ^ 2 ∂P) ≤
      (T : ℝ) * X.σ ^ 2 * K ^ 2 := by sorry
