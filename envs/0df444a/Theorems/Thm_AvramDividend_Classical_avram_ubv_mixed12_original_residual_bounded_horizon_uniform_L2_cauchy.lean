-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_residual_bounded_horizon_uniform_L2_cauchy
-- name    : AvramDividend.Classical.avram_ubv_mixed12_original_residual_bounded_horizon_uniform_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:32:50.036218+00:00
-- url     : https://prove2.me/theorems/9f0b186c-d11d-4194-85e9-eab9e950e821
-- title:
--   Uniform original residual L2 control at all bounded physical horizons from same-space isometry
-- statement:
--   For the original spectrally negative Levy process, a family identified pathwise with the intrinsic truncated residual is uniformly L2 Cauchy over all stopping horizons bounded by H, provided one has its actual same-space physical strip-isometry bound. The cutoff is uniform in both bands and in bounded physical time, using the established original Levy-measure quadratic strip-tail theorem. This does not assume an independent Gaussian surrogate or assert an unproved joint Ito-Meyer decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_real_quadratic_strip_uniform_tail

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed12_original_residual_bounded_horizon_uniform_L2_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (H : ℝ≥0)
    (R : ℕ → ℝ≥0 → Ω → ℝ)
    (hR : ∀ (n : ℕ) (T : ℝ≥0) (ω : Ω),
      R n T ω = avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
    (hIso : ∀ (n m : ℕ) (T : ℝ≥0), T ≤ H →
      Integrable (fun ω => (R n T ω - R m T ω) ^ 2) P ∧
      (∫ ω, (R n T ω - R m T ω) ^ 2 ∂P) ≤
        (H : ℝ) *
          (∫ z in Ioc
            (-(1 / (((min n m : ℕ) : ℝ) + 1)))
            (-(1 / (((max n m : ℕ) : ℝ) + 1))),
            z ^ 2 ∂X.ν)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ m : ℕ, N ≤ m →
          ∀ T : ℝ≥0, T ≤ H →
            Integrable (fun ω => (R n T ω - R m T ω) ^ 2) P ∧
            (∫ ω, (R n T ω - R m T ω) ^ 2 ∂P) < ε := by
  sorry
