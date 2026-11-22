-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_finiteactivity_original_continuous_gaussian_any_bounded_stop_initial_condexp_zero
-- name    : AvramDividend.Classical.avram_jump6_finiteactivity_original_continuous_gaussian_any_bounded_stop_initial_condexp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T23:01:45.921997+00:00
-- url     : https://prove2.me/theorems/58ed73ee-2a9f-4c04-b92f-892306bae316
-- title:
--   Construct original continuous Gaussian residual stopped at any bounded clock, L1 with time-zero conditional expectation zero
-- statement:
--   On the original filtered probability space of any Standing spectrally negative Lévy process with finite negative-jump mass, and for any right-continuous filtration stopping time τ bounded by positive natural horizon n, construct a continuous adapted Gaussian intrinsic residual process G which is the almost-sure pointwise limit of the physical original truncated Gaussian residuals, has mean zero at fixed times, and whose actual stopped Gτ is integrable with conditional expectation zero given the original initial filtration. No Gaussian witness process or optional-stopping assumption is added.
-- source:
--   Proved 0d7f9ed2 original Gaussian residual limit exists; Proved 33051068 original continuous centered martingale G; Proved c75b122d bounded true-clock initial conditional Gaussian martingale identity; root missing original physical stopped Ito source 15815eff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_bounded_true_stop_condexp_zero
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_finiteactivity_original_continuous_gaussian_any_bounded_stop_initial_condexp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (G t ω))) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      Integrable (fun ω => G (τ ω) ω) P ∧
      P[(fun ω => G (τ ω) ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by sorry
