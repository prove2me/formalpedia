-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
-- name    : AvramDividend.Classical.avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T01:03:38.704771+00:00
-- url     : https://prove2.me/theorems/2c95a423-175c-4a2f-9d73-27a09206d4e0
-- title:
--   Exact original Gaussian cutoff differences reduce to physical compensated jump differences
-- statement:
--   For any original process X, the difference of two source-exact intrinsic Gaussian residual truncations is exactly the opposite difference of two source-exact compensated bounded-mark jump sums. Drift, original X and large marks cancel pathwise. This is the first source-exact algebraic step towards a physical strip-isometry for the Gaussian residual.
-- source:
--   Algebraic consequence of original X truncation definitions, without any auxiliary Brownian and without large-mark moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_anoise17_original_residual_cutoff_diff_eq_compensator_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (t : ℝ≥0) (ω : Ω) :
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
      avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω =
    avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by
  sorry
