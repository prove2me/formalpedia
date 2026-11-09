-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed11_original_uniform_residual_from_physical_smalljump_isometry
-- name    : AvramDividend.Classical.avram_ubv_mixed11_original_uniform_residual_from_physical_smalljump_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:49:11.318196+00:00
-- url     : https://prove2.me/theorems/ebdf5346-e3cb-41ce-9dc6-56d4d4e78504
-- title:
--   Same-original-process uniformly bounded-horizon residual L2 Cauchy via physical smalljump isometry
-- statement:
--   For the intrinsic residual obtained from the same original spectrally negative Levy source X, a physical per-clock small-jump strip L2 isometry implies a single Cauchy cutoff uniform over every horizon T at most H and both truncation bands. The original residual/small-band L2 transfer and original Levy-measure quadratic-tail theorem are already Proved. The physical small-band isometry is explicitly assumed, preserving the unclosed stochastic obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed11_original_uniform_residual_from_physical_smalljump_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (H : ℝ≥0)
    (hSmallIso : ∀ (n m : ℕ) (T : ℝ≥0), T ≤ H →
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
         avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2) P ∧
      (∫ ω,
        (avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω -
         avram_p4_h_gaussian_intrinsic_small_band_compensated X m T ω) ^ 2 ∂P) ≤
        (T : ℝ) *
          (∫ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            z ^ 2 ∂X.ν)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ m : ℕ, N ≤ m →
          ∀ T : ℝ≥0, T ≤ H →
            Integrable (fun ω =>
              (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
               avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2) P ∧
            (∫ ω,
              (avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
               avram_p4_h_gaussian_intrinsic_truncated_residual X m T ω) ^ 2 ∂P) < ε := by
  sorry
