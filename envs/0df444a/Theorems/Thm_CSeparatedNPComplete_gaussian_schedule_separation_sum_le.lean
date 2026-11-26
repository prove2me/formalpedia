-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_le
-- name    : CSeparatedNPComplete.gaussian_schedule_separation_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:52:36.727228+00:00
-- url     : https://prove2.me/theorems/7d5a00b0-db2e-591c-bba1-774f8bb47e24
-- title:
--   CSeparated NPComplete: gaussian schedule separation sum le
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule separation sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L11-L15
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L11-L15

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_separation_sum_le (m : ℝ) (i : ℕ) {k l : ℕ}
    (hkl : k ≤ l) :
    gaussian_schedule_separation_sum m i k ≤ gaussian_schedule_separation_sum m i l := by sorry
