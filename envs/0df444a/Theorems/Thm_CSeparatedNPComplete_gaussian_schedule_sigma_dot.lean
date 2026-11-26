-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_sigma_dot
-- name    : CSeparatedNPComplete.gaussian_schedule_sigma_dot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:09.673413+00:00
-- url     : https://prove2.me/theorems/19046842-57ba-41ef-921d-fe3dbec8c56f
-- title:
--   CSeparated NPComplete: gaussian schedule sigma dot
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule sigma dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L68-L77
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L68-L77

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_sigma_dot {n : ℕ} (m : ℝ) (a : Vec n) {j : ℕ}
    (hj : j ≠ 0) :
    dot a (gaussian_schedule_sigma m j) =
      gaussian_schedule_separation_sum m j j * (m * dot a (canon_e (j - 1)) + dot a 1) := by sorry
