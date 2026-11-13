-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
-- name    : AvramDividend.Classical.avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:15:27.620459+00:00
-- url     : https://prove2.me/theorems/c3defb32-5612-4eae-9202-53386b6737f7
-- title:
--   Original finite-range stopped mixed Gaussian and compensated jump channels are integrable and initially centred
-- statement:
--   For every finite-range original-filtration stopping time up to the physical horizon under finite negative-jump activity, there exist the actual intrinsic Gaussian and compensated small-jump martingales, represented as limits of the canonical original Lévy cutoffs, with integrable stopped values and zero conditional expectation in the original initial filtration.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), same-source mixed Ito-Meyer stopped martingale construction, B31 and Proved JB20 8d6c7ead.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_finite_range_mixed_stopped_noise_pair
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
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
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (MG MJ : Ω → ℝ),
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
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ ω, MG ω = R (τ ω) ω) ∧
      (∀ ω, MJ ω = Jsmall (τ ω) ω) := by sorry
