-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
-- name    : AvramDividend.Classical.avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T23:06:32.055485+00:00
-- url     : https://prove2.me/theorems/20115e40-6783-469c-ba78-275d691e647b
-- title:
--   Original finite-activity intrinsic continuous Gaussian and compensated smallmark at any bounded stop are both initially eventwise centred
-- statement:
--   On the original probability space and right-continuous filtration of any Standing finiteactivity spectrally negative Lévy X, construct physical Gaussian G and original compensated small negative mark process Jsmall, with their intrinsic original X cutoff limits, G almost surely continuous, G(τ) and Jsmall(τ) integrable at any bounded right-continuous stopping clock τ, and for every original time-zero event A both true stopped integrals over A vanish. Do not assume a Gaussian or Poisson process or the desired stopped reward budget.
-- source:
--   Proved 0d7f9ed2,33051068,c75b122d,61f39bfe,1820407b. Needed source stochastic centring for finiteactivity positive-clock expected stopped dividend reward 15815eff and root 545c65ef.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_bounded_clock_continuous_gaussian_smallmark_both_eventwise_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ (G Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (G t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (𝓝 (Jsmall t ω))) ∧
      Integrable (fun ω => G (τ ω) ω) P ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, G (τ ω) ω ∂P) = 0 ∧
        (∫ ω in A, Jsmall (τ ω) ω ∂P) = 0) := by sorry
