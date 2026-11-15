-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
-- name    : AvramDividend.Classical.avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:04:03.662511+00:00
-- url     : https://prove2.me/theorems/194c4619-474b-4a58-82e9-444f77e64c5e
-- title:
--   Original stopped Gaussian and compensated jump grid gains are integrable and initially centred under bounded predictable weights
-- statement:
--   For one genuine original spectrally negative Levy source with finite negative jump activity, produce the global intrinsic Gaussian and compensated small jump martingales, and show on any deterministic finite grid, for any right-continuous stopping clock and source-filtration predictable weights with deterministic absolute bounds, the stopped gains are integrable and both have conditional expectation zero at initial information. The product integrability assumptions of B217 follow automatically from these bounded weights and the source fixed-time L1 property; no finite-range stopping clock is required.
-- source:
--   Proved B212 and JB21, via B217 and pinned Mathlib Integrable.bdd_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
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
      P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
