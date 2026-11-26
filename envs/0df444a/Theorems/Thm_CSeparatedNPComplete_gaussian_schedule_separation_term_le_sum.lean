-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_term_le_sum
-- name    : CSeparatedNPComplete.gaussian_schedule_separation_term_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:39.896596+00:00
-- url     : https://prove2.me/theorems/1a3629d0-62e3-550f-a188-420b6a5aec31
-- title:
--   CSeparated NPComplete: gaussian schedule separation term le sum
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule separation term le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L130-L135
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L130-L135

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_separation_term_le_sum (m : ℝ) {i j : ℕ} (hij : i < j) :
    (m ^ i - m ^ j) ^ 2 ≤ gaussian_schedule_separation_sum m j j := by sorry
