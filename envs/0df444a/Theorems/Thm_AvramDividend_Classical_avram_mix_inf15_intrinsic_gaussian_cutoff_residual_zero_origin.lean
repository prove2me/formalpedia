-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
-- name    : AvramDividend.Classical.avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T14:02:20.763452+00:00
-- url     : https://prove2.me/theorems/2e39b05b-85ea-4122-b293-0712619a67c7
-- title:
--   Original intrinsic Gaussian finite-cutoff residual vanishes at time zero without finite activity
-- statement:
--   The intrinsic truncated Gaussian residual constructed directly from the original Levy path has exact value zero at clock zero for every cutoff. No finite-activity hypothesis, auxiliary Gaussian process, or limit theorem is required. This supports the zero-clock vanishing property of future stopped mixed witnesses.
-- source:
--   Physical mixed infinite-activity witness zero-clock cancellation chain 5f12c023 -> f5e6e083; exact finite-cutoff initial identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n (0 : ℝ≥0) ω = 0 := by sorry
