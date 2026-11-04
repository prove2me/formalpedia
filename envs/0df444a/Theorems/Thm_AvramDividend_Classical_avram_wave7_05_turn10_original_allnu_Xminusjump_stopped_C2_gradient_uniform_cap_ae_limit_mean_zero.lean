-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_ae_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_ae_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:38:34.298323+00:00
-- url     : https://prove2.me/theorems/c40afe8e-2524-4cb7-901d-0d9d694dbe2a
-- title:
--   Original stopped C2 Gaussian source gradient a.e. limit centred by cap-driven uniform integrability
-- statement:
--   For the actual original SpectrallyNegativeLevy X, a same-space Gaussian projection with explicitly assumed decomposition, predictable stopped C2 reserve gradients uniformly bounded by K, and localised steps at most T, any almost everywhere limit of the single stopped Gaussian gain has expectation zero. The uniform integrability is deduced from source-specific variance cap and L2 seminorm bound, rather than assumed.
-- source:
--   Source-specific uniform cap L2 seminorm theorem; original stopped derivative Gaussian isometry and mean-zero theorem; pinned Mathlib Vitali convergence.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_L2_seminorm_bound
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original stopped C2 Gaussian gradient cap and a.e. limit yield zero mean. -/

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_ae_limit_mean_zero
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
    (hGbound : ∀ n ω, |G n ω| ≤ K)
    (L : Ω → ℝ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → Ω → ℝ := fun n ω =>
      M (τ n ω + h n) ω - M (τ n ω) ω
    (∀ᵐ ω ∂P, Tendsto (fun n => G n ω * V n ω) atTop (nhds (L ω))) →
      (∫ ω, L ω ∂P) = 0 := by sorry
