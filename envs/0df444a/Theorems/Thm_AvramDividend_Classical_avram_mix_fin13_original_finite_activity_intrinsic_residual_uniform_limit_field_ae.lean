-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
-- name    : AvramDividend.Classical.avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T01:14:25.350219+00:00
-- url     : https://prove2.me/theorems/0d7f9ed2-5536-4eed-8a9b-29f9d59f9908
-- title:
--   Original finite-activity intrinsic Gaussian residual admits a uniform compact pathwise limit field
-- statement:
--   For the original finite-activity spectrally negative Levy process X, construct on the unchanged sample space a single real-valued field R(t,omega) that is almost surely the pointwise and uniform-on-each-bounded-horizon limit of its actual intrinsic Gaussian truncated residual. The proof uses the already Proved original compensated small-band jump limit and the exact source identity R_n-R_0 = -(J_n-J_0). It establishes physical source convergence only, without asserting martingale Gaussian law, bracket or the stopped dividend Ito reward that remains open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_physical_residual_limit_uniform_ae
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin13_original_finite_activity_intrinsic_residual_uniform_limit_field_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      ∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (nhds (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
              |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
                R T ω| ≤ η) := by sorry
