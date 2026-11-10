-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_residual_limit_unique_ae
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_residual_limit_unique_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:00:40.864111+00:00
-- url     : https://prove2.me/theorems/0f2f4abf-04f2-4dc1-bd77-e4a4d54d0de7
-- title:
--   Unique same-space compact-uniform intrinsic Gaussian residual limit up to indistinguishability
-- statement:
--   For the original finite-activity Lévy process, the compact-uniform pathwise Gaussian residual field already constructed in 0d7f9ed2 is unique up to an almost-sure event simultaneously for all nonnegative times. This establishes a comparison principle for any later adapted canonical construction; it does not establish its martingale law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_intrinsic_residual_limit_unique_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
                R T ω| ≤ η)) ∧
      (∀ S : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (S T ω))) →
        ∀ᵐ ω ∂P, ∀ T : ℝ≥0, S T ω = R T ω) := by sorry
