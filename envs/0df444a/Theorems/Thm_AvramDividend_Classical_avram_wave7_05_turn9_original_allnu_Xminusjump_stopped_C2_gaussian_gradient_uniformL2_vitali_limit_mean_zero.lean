-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn9_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniformL2_vitali_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniformL2_vitali_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:16:08.198081+00:00
-- url     : https://prove2.me/theorems/639e1263-7364-49d5-9fdc-48522f7ddd8d
-- title:
--   Original stopped C2 Gaussian gradient martingale gains converge in mean under uniform L2
-- statement:
--   For canonical SpectrallyNegativeLevy X on the original Ω/P/𝓕 with an exact same-space zerojump Gaussian source Y and explicit X minus its jump and drift parts, stopped predictable discounted derivative integrands of w at the dividend-controlled original reserve produce mean-zero finite Gaussian gains. If these finite gains converge almost everywhere and their L2 seminorms are bounded uniformly, the limit has mean zero via uniform integrability and Vitali, with no independent Brownian model or Hessian hypotheses.
-- source:
--   Remotely Proved original X-minus-jumps stopped C2 Gaussian gradient finite sum zero-mean theorem from Wave7 turn7 and uniform L2-to-UI theorem UUID 6ecde2f8-f759-4772-8894-8a5887983551.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniformL2_vitali_limit_mean_zero
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
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n, ∀ i ∈ S n, G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (BG : ℕ → ι → ℝ)
    (hBG : ∀ n, ∀ i ∈ S n, 0 ≤ BG n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ BG n i)
    (L : Ω → ℝ) (C₂ : ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      M (τ n i ω + h n i) ω - M (τ n i ω) ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω * V n i ω
    (∀ n, eLpNorm (Q n) (2 : ℝ≥0∞) P ≤ C₂) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    (∫ ω, L ω ∂P) = 0 := by sorry
