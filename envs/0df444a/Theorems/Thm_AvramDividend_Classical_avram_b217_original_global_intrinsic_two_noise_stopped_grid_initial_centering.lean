-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b217_original_global_intrinsic_two_noise_stopped_grid_initial_centering
-- name    : AvramDividend.Classical.avram_b217_original_global_intrinsic_two_noise_stopped_grid_initial_centering
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:01:19.831196+00:00
-- url     : https://prove2.me/theorems/b1cdcbc5-5545-453a-9749-c3e5c588d2a5
-- title:
--   One global original intrinsic two-martingale pair centres every genuine stopped predictable finite-grid gain
-- statement:
--   Original finite-negative-jump-activity Levy process admits one global same-filtration intrinsic Gaussian martingale R and compensated negative-jump martingale J, both limits of the source cutoff expressions, such that every finite deterministic time grid with any genuine right-continuous stopping clock and adapted predictable Gaussian/jump weights gives two integrable, initially conditionally centered stopped gains, whenever the actual weighted products are integrable. The stopping clock need not have finite range. Inputs are the genuine original process and its filtration, without an independent comparison source.
-- source:
--   B212 and JB21 verified Proved; source-specific refinement of B216 true stopped cash mesh noise, no finite-range stop assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b217_original_global_intrinsic_two_noise_stopped_grid_initial_centering
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
        (hGprod : ∀ i ∈ S, Integrable
          (fun ω => (if τ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) P)
        (hJprod : ∀ i ∈ S, Integrable
          (fun ω => (if τ ω ≤ a i then 0 else WJ i ω) *
            (Jsmall (b i) ω - Jsmall (a i) ω)) P),
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
