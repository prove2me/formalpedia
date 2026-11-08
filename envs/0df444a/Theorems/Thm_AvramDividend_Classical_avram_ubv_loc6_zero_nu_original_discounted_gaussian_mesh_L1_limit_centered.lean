-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_zero_nu_original_discounted_gaussian_mesh_L1_limit_centered
-- name    : AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_discounted_gaussian_mesh_L1_limit_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:38:32.162507+00:00
-- url     : https://prove2.me/theorems/65de125a-1c21-43fd-8363-98e257301e55
-- title:
--   Physical zero-jump stopped discounted Gaussian mesh L1 limit is centred
-- statement:
--   For the actual original zero-negative-jump Levy process, its discounted pre-right-dividend gradient stopped Gaussian physical mesh has a zero-mean integrable limit whenever the bounded stopped-grid approximations converge in L1. No alternate Gaussian process or jump representation is needed.
-- source:
--   Specialise the Proved original all-nu source-exact Gaussian L1 limit theorem with Y=X and zero jump paths.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_C2_mesh_L1_mean_zero

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_discounted_gaussian_mesh_L1_limit_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
    (K : ℕ → ι → ℝ) (hK : ∀ n, ∀ i ∈ S n, 0 ≤ K n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ K n i)
    (M : Ω → ℝ) (hMI : Integrable M P) :
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω *
        (X.X (τ n i ω + h n i) ω -
          X.X (τ n i ω) ω - (h n i : ℝ) * X.c)
    Tendsto (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, M ω ∂P) = 0 := by sorry
