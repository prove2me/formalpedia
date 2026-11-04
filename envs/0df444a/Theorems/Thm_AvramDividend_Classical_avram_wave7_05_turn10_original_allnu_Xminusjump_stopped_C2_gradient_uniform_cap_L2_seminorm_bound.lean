-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_L2_seminorm_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_L2_seminorm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:13:31.294064+00:00
-- url     : https://prove2.me/theorems/d0c7ce0a-d5f7-4603-84a1-c1c8cbffba3d
-- title:
--   Original stopped C2 Gaussian source gradient uniform L2 norm derived from deterministic cap and time bound
-- statement:
--   For the original Lévy X, original controlled reserve and explicitly same-space Gaussian decomposition, a uniform cap K on the predictable derivative at bounded source stopping times and step upper bound T yield a uniform L2 seminorm bound of each stopped Gaussian gain by sqrt(T sigma² K²). This supplies the precise quantitative uniform-integrability hypothesis of the prior remotely Proved Vitali Gaussian expectation-zero theorem without assuming an L2 bound separately.
-- source:
--   Canonical original source Gaussian stopped isometry, accepted actual source gradient cap variance theorem, Mathlib MemLp.eLpNorm_eq_integral_rpow_norm.

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_sigma_variance_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_L2_seminorm_bound
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
    ∀ n, eLpNorm (fun ω => G n ω * V n ω) (2 : ℝ≥0∞) P ≤
      ENNReal.ofReal (Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2)) := by sorry
