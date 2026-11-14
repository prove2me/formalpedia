-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b81_original_jumpfree_cell_large_mark_sum_constant
-- name    : AvramDividend.Classical.avram_b81_original_jumpfree_cell_large_mark_sum_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:05:38.232386+00:00
-- url     : https://prove2.me/theorems/9917d1c1-d718-4a0d-9a1b-5f391c240264
-- title:
--   Original finite large negative-jump source sum constant on true jumpfree physical interval
-- statement:
--   The Proved original source large-negative-jump integral is the physical finite sum over exactly the actual original negative source marks whose jump amplitude is at most minus one by time T. For two physical ordered source clocks s<=t with no jump of original X in (s,t], the counted finite mark-time sets at t and s coincide by Finset.ext and the no-mark assumption. Therefore the original large-jump source sum has exactly the same value at those times. This directly supplies B78's hLarge assumption on a marked jumpfree selected interior cell, without modifying the sample path, using a surrogate jump process, or assuming global negative mark second moments. It applies to random s,t pointwise once the no-mark condition is established.
-- source:
--   Proved avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum; original physical source negative marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b81_original_jumpfree_cell_large_mark_sum_constant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ω : Ω)
    (hNoJump : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X s ω := by sorry
