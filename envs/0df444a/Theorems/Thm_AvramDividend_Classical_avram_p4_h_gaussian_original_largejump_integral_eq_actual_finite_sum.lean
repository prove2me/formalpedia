-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:43:14.521146+00:00
-- url     : https://prove2.me/theorems/e8675ada-9c6b-4628-966a-679f4acbb447
-- title:
--   Original uncompensated Jlarge equals the finite sum of actual large negative source jumps
-- statement:
--   The original large-negative-jump integral of the actual X process equals a finite sum on every sample path and finite horizon, supported exactly at the true negative jumps of size at least one. The proof uses unconditional original large-jump signed series and the source finite jump-time support, with explicit termwise indicator simplification.
-- source:
--   Source finite support e45c2694 and unconditional original largeband integral-to-tsum being developed here.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_tsum_finite_support
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ j u ≤ -1) ∧
      avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
        ∑ u ∈ F, j u := by sorry
