-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_diagonal_mono
-- name    : CSeparatedNPComplete.gaussian_schedule_separation_sum_diagonal_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:27.197198+00:00
-- url     : https://prove2.me/theorems/a285841e-a84f-5303-9dac-eded85ad2037
-- title:
--   CSeparated NPComplete: gaussian schedule separation sum diagonal mono
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule separation sum diagonal mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L59-L66
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L59-L66

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_separation_sum_diagonal_mono {m : ℝ} (hm : 2 ≤ m)
    {i j : ℕ} (hij : i ≤ j) :
    gaussian_schedule_separation_sum m i i ≤ gaussian_schedule_separation_sum m j j := by sorry
