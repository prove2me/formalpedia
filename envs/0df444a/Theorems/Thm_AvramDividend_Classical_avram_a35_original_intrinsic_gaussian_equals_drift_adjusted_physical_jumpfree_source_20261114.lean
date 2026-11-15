-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_drift_adjusted_physical_jumpfree_source_20261114
-- name    : AvramDividend.Classical.avram_a35_original_intrinsic_gaussian_equals_drift_adjusted_physical_jumpfree_source_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:10:34.013949+00:00
-- url     : https://prove2.me/theorems/e0723c3f-89d2-454b-b105-f124f23c4062
-- title:
--   Original finite-activity intrinsic Gaussian cutoff limit equals original Lévy path minus signed drift and actual complete physical jump series
-- statement:
--   For the original physical finite-negative-activity Lévy source, the intrinsic Gaussian cutoff limit is exactly the original source path minus its Lévy finite-activity signed drift and minus every actual marked jump, simultaneously at every nonnegative time on one source-probability conull event.
-- source:
--   Proved A22 original full physical jump-series cutoff limit 7b926252; Proved B84 cutoff signed moment limit 345e9ec7; intrinsic Gaussian residual definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a35_original_intrinsic_gaussian_equals_drift_adjusted_physical_jumpfree_source_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω =
        X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) := by sorry
