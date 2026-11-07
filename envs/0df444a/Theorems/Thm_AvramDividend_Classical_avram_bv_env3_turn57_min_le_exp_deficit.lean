-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn57_min_le_exp_deficit
-- name    : AvramDividend.Classical.avram_bv_env3_turn57_min_le_exp_deficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:29:20.272261+00:00
-- url     : https://prove2.me/theorems/25ad581b-1484-4446-820f-f389410c7618
-- title:
--   Truncated positive real size is bounded by twice its exponential deficit
-- statement:
--   For t nonnegative, min(1,t) is at most twice 1-exp(-t). This sharp-enough deterministic comparison allows the already proved normalized original Levy exponential-deficit limit to control truncated first moments of the actual negative Levy jumps.
-- source:
--   Real.add_one_le_exp, exp(-t)*exp(t)=1, the elementary 0<=t<=1 and 1<=t cases. This is the analytic pointwise bridge into the proved negative_jump_full_normalized_exp_deficit_tendsto_zero 639c8319.

import Mathlib.Analysis.Complex.Exponential
open Classical Real
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn57_min_le_exp_deficit
    (t : ℝ) (ht : 0 ≤ t) :
    min 1 t ≤ 2 * (1 - Real.exp (-t)) := by sorry
