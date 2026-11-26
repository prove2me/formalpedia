-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_sum_scaled_le
-- name    : CSeparatedNPComplete.gaussian_schedule_separation_sum_scaled_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:13.937379+00:00
-- url     : https://prove2.me/theorems/871c58ca-9781-5a9e-be41-3f8fd9cfa25c
-- title:
--   CSeparated NPComplete: gaussian schedule separation sum scaled le
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule separation sum scaled le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L48-L57
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L48-L57

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_separation_sum_scaled_le {m : ℝ} {i j : ℕ}
    (hm : 2 ≤ m) (hij : i < j) :
    (m + 1) * gaussian_schedule_separation_sum m i i ≤
      gaussian_schedule_separation_sum m j j := by sorry
