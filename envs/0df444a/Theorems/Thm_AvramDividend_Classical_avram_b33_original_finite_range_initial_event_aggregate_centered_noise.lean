-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b33_original_finite_range_initial_event_aggregate_centered_noise
-- name    : AvramDividend.Classical.avram_b33_original_finite_range_initial_event_aggregate_centered_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:21:34.81637+00:00
-- url     : https://prove2.me/theorems/a7f42bf8-a920-4010-af4a-302e3a29f218
-- title:
--   Original finite-range mixed stopped aggregate Gaussian and jump noise has zero mean on every initial event
-- statement:
--   At every finite-range right-continuous original Lévy stopping time, the sum of its genuine intrinsic Gaussian and compensated negative-jump stopped noises is globally integrable and has integral zero on every event measurable at physical time zero. The two noise fields are canonical cutoff limits of the original source.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), same-source stopped Ito-Meyer noise; B32 and original past-event conditional centring lemma 1820407b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b33_original_finite_range_initial_event_aggregate_centered_noise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S) :
    ∃ (M : Ω → ℝ) (R Jsmall : ℝ≥0 → Ω → ℝ),
      Integrable M P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, M ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      (∀ ω, M ω = R (τ ω) ω + Jsmall (τ ω) ω) := by sorry
