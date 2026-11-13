-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva91_original_mapped_levy_compensator_time_zero_atom_null_any_horizon
-- name    : AvramDividend.Classical.avram_bva91_original_mapped_levy_compensator_time_zero_atom_null_any_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:53:14.40213+00:00
-- url     : https://prove2.me/theorems/5dbc070e-adcf-4154-9c4d-53225ea8679b
-- title:
--   Original mapped negative-mark compensator time clock has no initial atom for any horizon
-- statement:
--   For every nonnegative horizon S, the literal original BV negative-mark compensator time measure obtained by restricting real Lebesgue volume to [0,S] and mapping Real.toNNReal has no atom at time zero. The preimage of zero under Real.toNNReal is the nonpositive real half-line, whose intersection with [0,S] is singleton zero of null Lebesgue volume. Enables annihilating zero-clock supported kernels even when the outer source clock runs beyond zero, as required for immediate-ruin M_n(S).

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva91_original_mapped_levy_compensator_time_zero_atom_null_any_horizon
    (S : ℝ≥0) :
    (((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal)
      ({0} : Set ℝ≥0) = 0 := by sorry
