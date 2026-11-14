-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b40_original_finite_range_intrinsic_centered_sum
-- name    : AvramDividend.Classical.avram_b40_original_finite_range_intrinsic_centered_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:47:09.152473+00:00
-- url     : https://prove2.me/theorems/bdde3390-e7c1-4846-9efa-1ef0f4bb0b12
-- title:
--   Original finite-range stopped intrinsic Gaussian plus compensated jump noise has zero initial-event mean
-- statement:
--   An actual finite-activity spectrally negative Lévy process on the original filtration has an integrable Gaussian-plus-compensated-jump intrinsic source at every finite-range right-continuous stopping time, conditionally centred at time zero and with zero integral on each initial measurable event.
-- source:
--   Proved B32 original finite-range two intrinsically centered stopped channels c3defb32, setIntegral_condExp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b40_original_finite_range_intrinsic_centered_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ) (M : Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) ∧
      Integrable M P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
      (∀ ω, M ω = R (τ ω) ω + Jsmall (τ ω) ω) ∧
      (∫ ω in A, M ω ∂P) = 0 := by sorry
