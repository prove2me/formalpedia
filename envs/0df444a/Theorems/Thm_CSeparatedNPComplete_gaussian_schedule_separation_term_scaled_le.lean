-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_separation_term_scaled_le
-- name    : CSeparatedNPComplete.gaussian_schedule_separation_term_scaled_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:24.075436+00:00
-- url     : https://prove2.me/theorems/14f73865-f8bf-5c36-b929-2a8829f709fd
-- title:
--   CSeparated NPComplete: gaussian schedule separation term scaled le
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule separation term scaled le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L29-L46
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L29-L46

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_separation_term_scaled_le {m : ℝ} {k i j : ℕ}
    (hm : 2 ≤ m) (hki : k < i) (hij : i < j) :
    (m + 1) * (m ^ i - m ^ k) ^ 2 ≤ (m ^ j - m ^ k) ^ 2 := by sorry
