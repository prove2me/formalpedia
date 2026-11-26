-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot_positive_all
-- name    : CSeparatedNPComplete.gaussian_schedule_sigma_dot_positive_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:32.951208+00:00
-- url     : https://prove2.me/theorems/6bdbe871-8941-4403-abfe-9c6d1f1b2997
-- title:
--   CSeparated NPComplete: gaussian schedule sigma dot positive all
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule sigma dot positive all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L88-L98
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L88-L98

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_sigma_dot_positive_all {n : ℕ} {m : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m) (j : ℕ) :
    0 < dot a (gaussian_schedule_sigma m j) := by sorry
