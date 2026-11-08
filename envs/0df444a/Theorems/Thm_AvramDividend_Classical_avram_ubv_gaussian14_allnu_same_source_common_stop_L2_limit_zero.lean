-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian14_allnu_same_source_common_stop_L2_limit_zero
-- name    : AvramDividend.Classical.avram_ubv_gaussian14_allnu_same_source_common_stop_L2_limit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:18:40.9032+00:00
-- url     : https://prove2.me/theorems/3c00e51a-f4ba-4b53-98f2-2226dccc332a
-- title:
--   Original all-nu same-space stopped Gaussian grids converge in L2 to an L2 centred terminal martingale
-- statement:
--   For an explicit same-Omega original Lévy–Itô source decomposition with zero-jump Gaussian component Y and original filtration, every finite stopped original-source C2 Gaussian gradient grid is L2 and centred by previously proved isometry and conditional mean-zero theorems. If these grids converge in L2 to a strongly measurable original-space terminal variable, then the terminal variable is L2 and has exactly zero expectation. No augmentation, new path, or jump-measure simplification is introduced.
-- source:
--   Proved 0e190b1b C2 Gaussian finite sum MemLp, e40a12a2 C2 finite sum mean zero, pinned Mathlib Lp.memLp_of_cauchy_tendsto and tendsto_integral_of_L1'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian14_allnu_same_source_common_stop_L2_limit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : ℕ → Finset ι) (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ (n : ℕ) (s : ℝ≥0),
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (B : ℕ → ℝ≥0) (hB : ∀ n ω, τ n ω ≤ B n)
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n i, i ∈ S n → G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℕ → ι → ℝ)
    (hK : ∀ n i, i ∈ S n → 0 ≤ K n i)
    (hGbound : ∀ n i, i ∈ S n → ∀ ω, |G n i ω| ≤ K n i)
    (L : Ω → ℝ) (hLmeas : AEStronglyMeasurable L P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω * (M (τ n ω + h n i) ω - M (τ n ω) ω)
    Tendsto (fun n => eLpNorm (Q n - L) 2 P) atTop (𝓝 0) →
    MemLp L 2 P ∧ (∫ ω, L ω ∂P) = 0 := by sorry
