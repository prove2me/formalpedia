-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_mu_distance
-- name    : CSeparatedNPComplete.gaussian_schedule_mu_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:28.233826+00:00
-- url     : https://prove2.me/theorems/45904d8e-d9f7-4a5f-b5b1-a07db46768f0
-- title:
--   CSeparated NPComplete: gaussian schedule mu distance
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule mu distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L79-L86
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L79-L86

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_mu_distance {n : ℕ} (a : Vec n) (m : ℝ) (i j : ℕ) :
    dot a (sqVec (gaussian_schedule_mu m i - gaussian_schedule_mu m j)) =
      (m ^ i - m ^ j) ^ 2 * dot a 1 := by sorry
