-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_ge_1
-- name    : CSeparatedNPComplete.gaussian_schedule_separation_sum_ge_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:59.780801+00:00
-- url     : https://prove2.me/theorems/0dd0f56c-ca8e-54d7-8d6d-9aaabe16cec3
-- title:
--   CSeparated NPComplete: gaussian schedule separation sum ge 1
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule separation sum ge 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L17-L27
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L17-L27

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_separation_sum_ge_1 {m : ℝ} {j : ℕ}
    (hm : 2 ≤ m) (hj : 0 < j) :
    1 ≤ gaussian_schedule_separation_sum m j j := by sorry
