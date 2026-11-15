-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a56_original_gaussian_true_stationary_independent_increments_20261114
-- name    : AvramDividend.Classical.avram_a56_original_gaussian_true_stationary_independent_increments_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:17:02.575629+00:00
-- url     : https://prove2.me/theorems/84650d04-cbe9-42e6-a4d3-7d009f14de55
-- title:
--   Original Gaussian source has raw independent and stationary IdentDistrib increments
-- statement:
--   The original intrinsic Gaussian residual has a raw-adapted zero-start representative with continuous paths on one conull event and independent stationary increments in the precise IdentDistrib sense on its original filtered probability space.
-- source:
--   A41 original source assembly and A55 law-witness bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a41_original_continuous_gaussian_source_raw_adapted_independent_stationary_20261114
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a56_original_gaussian_true_stationary_independent_increments_20261114
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
      (∀ s t, s ≤ t →
        Indep (MeasurableSpace.comap
          (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P) ∧
      (∀ s t, s ≤ t →
        IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P) := by sorry
