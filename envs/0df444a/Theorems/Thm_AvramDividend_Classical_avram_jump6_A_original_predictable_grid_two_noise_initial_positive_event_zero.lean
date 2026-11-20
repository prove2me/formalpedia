-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_predictable_grid_two_noise_initial_positive_event_zero
-- name    : AvramDividend.Classical.avram_jump6_A_original_predictable_grid_two_noise_initial_positive_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:45:49.398128+00:00
-- url     : https://prove2.me/theorems/14078838-50d0-4133-8b2f-a2c2fe5dfcf2
-- title:
--   Original bounded predictable Gaussian and negative-mark grid weighted gains have zero integral on every initial positive-clock event
-- statement:
--   Construct the genuine Lévy intrinsic Gaussian and finite-activity negative-smallmark martingales; for any bounded predictable grid weights and a bounded stopped physical clock, both stochastic gains are integrable, conditionally centred and jointly have exactly zero integral on every right-continuous initial-filtration event restricted to strictly positive stopping clock. Applies to spatial Itô weight derivatives after bounded localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_predictable_grid_two_noise_initial_positive_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
 :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      ∀ {ι : Type*} (S : Finset ι)
        (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
        (hab : ∀ i ∈ S, a i ≤ b i)
        (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
        (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
        (τ : Ω → ℝ≥0)
        (hτstop : IsStoppingTime 𝓕.rightCont
          (fun ω => (τ ω : WithTop ℝ≥0)))
        (LG LJ : ℝ) (hLG : 0 ≤ LG) (hLJ : 0 ≤ LJ)
        (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
        (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ),
      let MG : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)
      let MJ : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)
      Integrable MG P ∧
      P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable MJ P ∧
      P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A ∩ {η : Ω | τ η ≠ 0}, MG ω + MJ ω ∂P) = 0)
      := by sorry
