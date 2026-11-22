-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_finiteactivity_intrinsic_continuous_gaussian_centered_martingale_exists
-- name    : AvramDividend.Classical.avram_jump6_original_finiteactivity_intrinsic_continuous_gaussian_centered_martingale_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T22:44:18.522167+00:00
-- url     : https://prove2.me/theorems/81277cbe-d8d8-4c98-9919-9e513ea4b939
-- title:
--   Existence of a continuous adapted centred intrinsic Gaussian martingale with independent stationary increments on the original finite-activity Lévy space
-- statement:
--   For any original Standing spectrally negative Lévy process with finite negative jump activity, construct a uniformly sourced intrinsic Gaussian residual R and a single same-space adapted version G with continuous sample paths almost surely, zero initial value, mean zero and L1 at each fixed time, martingale conditional expectation in the original right-continuous filtration, independent increments from the original past, and stationary increment laws. No extra residual process or Gaussian companion hypotheses are assumed.
-- source:
--   Directly combines Proved avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae 0d7f9ed2-5536-4eed-8a9b-29f9d59f9908 and Proved avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114 33051068-7023-4304-b859-14a07b0904be; source for Avram stopped finiteactivity original Gaussian Itô in 15815eff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
import Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_finiteactivity_intrinsic_continuous_gaussian_centered_martingale_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ (R G : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (𝓝 (R t ω))) ∧
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ s T : ℝ≥0,
        Indep (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
          (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
            Measure.map Z P) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by sorry
