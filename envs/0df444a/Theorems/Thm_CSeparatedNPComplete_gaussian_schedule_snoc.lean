-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_snoc
-- name    : CSeparatedNPComplete.gaussian_schedule_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:44.703025+00:00
-- url     : https://prove2.me/theorems/cbadcded-7f21-5a2d-a2cf-cf6595b2ae45
-- title:
--   CSeparated NPComplete: gaussian schedule snoc
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L160-L163
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L160-L163

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_snoc {n : ℕ} (m : ℝ) (k : ℕ) :
    gaussian_schedule (n := n) m (k + 1) =
      gaussian_schedule m k ++ [gaussian_schedule_class m k] := by sorry
