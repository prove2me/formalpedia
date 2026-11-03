-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_gaussian_gradient_L1_localisation_auto_predictable_mean_zero
-- name    : AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_gaussian_gradient_L1_localisation_auto_predictable_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:16:00.870169+00:00
-- url     : https://prove2.me/theorems/8e3645d1-40e7-42ac-b7e0-354ea5e738dd
-- title:
--   Original all-jump Gaussian source bounded C2 gradient L1 mesh limit automatically predictable and centred
-- statement:
--   For the original arbitrary-jump X and an explicitly same-space/same-filtration Gaussian component Y, every bounded stopped original-reserve discounted C2 gradient mesh is integrable and centred with automatically proven coefficient measurability. Any integrable L1 limit M of these meshes is centred. No separate global coefficient-measurability hypothesis is needed.
-- source:
--   Imports authored source gradient finite-multistop automatic predictability lemma UUID 1efcff85-6921-44f4-bda6-846b3e7a045c (must be Proved) and pinned Mathlib tendsto_integral_of_L1. Existence of source Gaussian decomposition and L1 convergence are explicit hypotheses.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_gaussian_gradient_L1_localisation_auto_predictable_mean_zero
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
