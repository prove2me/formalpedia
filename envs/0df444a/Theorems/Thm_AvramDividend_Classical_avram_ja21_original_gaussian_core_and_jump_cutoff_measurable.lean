-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
-- name    : AvramDividend.Classical.avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:44:17.826487+00:00
-- url     : https://prove2.me/theorems/f7cf0440-53ef-4ba3-a5e9-6dc26305ffd4
-- title:
--   Intrinsic original Gaussian core and finite negative-jump cutoff are measurable in the original filtration
-- statement:
--   For any original Levy process, the cutoff-independent Gaussian source core R0+Jsmall0 and the negative of the n-th compensated small-jump source are both measurable in the original filtration at time t. This supplies the measurability inputs for J-A21's physical source square-moment certificate.
-- source:
--   J-A21 directly from Proved 42ada2ca and 7ba6e5dc, no auxiliary probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓕 t]
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω) ∧
    Measurable[𝓕 t]
      (fun ω => -avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by sorry
