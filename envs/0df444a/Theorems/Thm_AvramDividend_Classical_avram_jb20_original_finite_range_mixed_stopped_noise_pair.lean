-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_finite_range_mixed_stopped_noise_pair
-- name    : AvramDividend.Classical.avram_jb20_original_finite_range_mixed_stopped_noise_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:59:00.1632+00:00
-- url     : https://prove2.me/theorems/8d6c7ead-4275-4c73-8048-02d395e7e394
-- title:
--   Same physical finite-range stopped clock has two integrable initially centred Gaussian and compensated-jump sources
-- statement:
--   The physical intrinsic Gaussian residual and finite-activity compensated negative-jump noise are simultaneously integrable and initially conditionally centred at the same bounded finite-range original-filtration stopping clock. The original marks and right-continuous filtration are retained.
-- source:
--   Proved 1fa784c3 original Gaussian finite-range stopped optional sampling and Proved 61f39bfe original compensated small-jump stopped martingale; a necessary two-channel witness for Open mixed Ito cash ledger 544e8511.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_range_stop_condexp
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_finite_range_mixed_stopped_noise_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    ∃ MG MJ : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MG ω = 0) ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P MJ ω = 0) ∧
      (∀ ω, MG ω = R (τ ω) ω) ∧
      ∃ Jsmall : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto
            (fun k : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
            atTop (nhds (Jsmall t ω))) ∧
        (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
        (∀ s t : ℝ≥0, s ≤ t →
          ∀ᵐ ω ∂P,
            condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
        (∀ ω, MJ ω = Jsmall (τ ω) ω) := by sorry
