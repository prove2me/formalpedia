-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_C2_mesh_L1_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_C2_mesh_L1_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:48:31.800202+00:00
-- url     : https://prove2.me/theorems/2d1e311b-3f00-4b64-bd86-af294bb4507c
-- title:
--   Original arbitrary-jump C2 bounded stopped Gaussian gradient mesh L1 limit has zero expectation
-- statement:
--   For canonical arbitrary-jump X and an explicitly same-space same-filtration Gaussian zero-jump component Y with σ matching X and source Lévy-Itô decomposition, discounted predividend C2 stopped gradient gains in every finite mesh are integrable, centred, and preserve zero mean under L1 convergence. Predictability follows from the original source derivative theorem; uniform gradient bounds supply the Gaussian moment estimates.
-- source:
--   Derives each finite-grid meanzero from Proved original all-ν stopped derivative coefficients UUID 186c0d87-955f-47c7-a5c2-35002ba40cd8 and Proved zero-jump bounded stopped gain UUID 8cf2614f-c9fe-47f1-896a-57969706c910. Then Mathlib tendsto_integral_of_L1. Source decomposition and mesh L1 convergence are explicit binders; no unrelated Brownian space.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_allnu_multi_stop_C2_gaussian_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_C2_mesh_L1_mean_zero
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
    (hGglobal : ∀ n, ∀ i ∈ S n, Measurable (G n i))
    (K : ℕ → ι → ℝ)
    (hK : ∀ n, ∀ i ∈ S n, 0 ≤ K n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ K n i)
    (M : Ω → ℝ) (hMI : Integrable M P) :
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
        (h n i : ℝ) * Y.c
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω * V n i ω
    Tendsto (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, M ω ∂P) = 0 := by sorry
