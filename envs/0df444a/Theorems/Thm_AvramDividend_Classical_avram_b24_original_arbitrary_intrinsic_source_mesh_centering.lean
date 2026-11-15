-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_source_mesh_centering
-- name    : AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_source_mesh_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:55:28.026574+00:00
-- url     : https://prove2.me/theorems/b0c2f353-bfd4-4ee0-8315-9f2e62646918
-- title:
--   Every original same-source intrinsic Gaussian and negative-mark stopped bounded mesh has centred integrable gains
-- statement:
--   Use the proved original intrinsic two-channel stopped finite mesh centring theorem for canonical R and small-negative compensated J, then transfer both integrability and zero conditional expectation to every R/Jsmall pair that agrees with exactly the same original Lévy source residual limit on the same probability space. Preserves stopped event masks and bounded predictable weights, not post-ruin continuation.
-- source:
--   B218 proved original intrinsic Gaussian compensated-jump stopped finite mesh centring, and the same-source almost-everywhere uniqueness of endpoint limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b218_original_bounded_weight_intrinsic_two_noise_stopped_grid_centering
import Theorems.Thm_AvramDividend_Classical_avram_b24_intrinsic_same_source_noise_limits_unique
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_source_mesh_centering
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    ∀ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
      (WG WJ : ℕ → Ω → ℝ)
      (hab : ∀ i ∈ S, a i ≤ b i)
      (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
      (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
      (σ : Ω → ℝ≥0)
      (hσstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (σ ω : WithTop ℝ≥0)))
      (LG LJ : ℝ) (hLG : 0 ≤ LG) (hLJ : 0 ≤ LJ)
      (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG)
      (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ),
      let MG : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
          (R (b i) ω - R (a i) ω)
      let MJ : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)
      Integrable MG P ∧
      P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      Integrable MJ P ∧
      P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
