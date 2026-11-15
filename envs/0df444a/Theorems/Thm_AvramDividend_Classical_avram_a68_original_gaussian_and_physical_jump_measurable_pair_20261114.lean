-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
-- name    : AvramDividend.Classical.avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:53:14.71135+00:00
-- url     : https://prove2.me/theorems/81f53bc8-e298-4242-ae0f-731d6fc1c8e4
-- title:
--   Measurable original raw Gaussian and physical marked jump total representatives with source identity
-- statement:
--   For the original finite-activity spectrally negative Levy process, obtain measurable versions H of its intrinsic Gaussian residual R_t and J of its original actual causal jump sum. Use the globally raw-adapted Gaussian representative (Proved A24) and define J as the physical source X_t minus compensated finite-activity drift and H. Proved A35 identifies J almost everywhere with the actual marked jump sum. The physical source decomposition holds for the chosen representatives on every path. No independence or new probability space is assumed.
-- source:
--   Proved f8000f9d original raw-adapted Gaussian representative, 6366b3de actual source jump series identity, and X.adapted. This isolates genuinely source-measurable versions for A65 without assuming jump/Gaussian independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a68_original_gaussian_and_physical_jump_measurable_pair_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) (t : ℝ≥0) :
    ∃ H J : Ω → ℝ,
      Measurable H ∧ Measurable J ∧
      (H =ᵐ[P] R t) ∧
      (J =ᵐ[P] fun ω =>
        ∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0) ∧
      (∀ ω, H ω + J ω =
        X.X t ω -
          (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by sorry
