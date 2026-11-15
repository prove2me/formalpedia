-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
-- name    : AvramDividend.Classical.avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:22:19.457+00:00
-- url     : https://prove2.me/theorems/33051068-7023-4304-b859-14a07b0904be
-- title:
--   Original finite-activity intrinsic Gaussian residual admits continuous-ae raw-adapted zero-start centred L1 martingale with independent stationary increments
-- statement:
--   On the original filtered probability space, the intrinsic finite-activity Gaussian residual has a zero-start raw adapted representative with continuous sample paths almost surely, independent future and stationary increments, integrable centred marginals and right-continuous filtration martingale conditional means.
-- source:
--   Proved A41 original continuous raw adapted independent stationary source process, A42 conull martingale transfer, and Proved A21 source centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a43_original_gaussian_continuous_raw_adapted_centered_martingale_indep_stationary_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω)) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap
          (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by sorry
