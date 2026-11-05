-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:35:47.655589+00:00
-- url     : https://prove2.me/theorems/75c91fbd-a90d-4b6a-981d-fabffffd8271
-- title:
--   Original truncated Gaussian residual L2 Cauchy energy equals actual compensated small-jump energy
-- statement:
--   For two cutoffs of the original pathwise residual M^c_n, the difference cancels the exact original X.X drift and large-jump integral, leaving precisely the negative of the difference of original compensated small-jump integrals. Hence the squared integrability conditions are equivalent and their second-moment integrals are exactly equal on the same original probability space P. This is the missing algebraic bridge for P4-G's prospective genuine smalljump L2 Cauchy interface; it makes no independent Gaussian or Poisson-law assumption.
-- source:
--   Published P4-H original residual definition 33b0fa2b and original compensated finite band 66a113ed; pointwise ring, Lean integrability/congruence on original P.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_residual_cutoff_difference_L2_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n m : ℕ) (t : ℝ≥0) :
    (Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ↔
     Integrable (fun ω : Ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω) ^ 2) P) ∧
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
       avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
    (∫ ω : Ω,
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
       avram_p4_h_gaussian_intrinsic_small_band_compensated X m t ω) ^ 2 ∂P) := by sorry
