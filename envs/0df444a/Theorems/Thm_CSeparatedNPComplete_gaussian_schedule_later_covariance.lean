-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_later_covariance
-- name    : CSeparatedNPComplete.gaussian_schedule_later_covariance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:36.445049+00:00
-- url     : https://prove2.me/theorems/0f933904-499f-43d6-aa4a-934c18f49aeb
-- title:
--   CSeparated NPComplete: gaussian schedule later covariance
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule later covariance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L100-L128
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L100-L128

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_later_covariance {n : ℕ} {m : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {i j : ℕ} (hij : i < j) :
    dot a (gaussian_schedule_sigma m i) ≤ dot a (gaussian_schedule_sigma m j) := by sorry
