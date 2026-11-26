-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_pair_hinge_before
-- name    : CSeparatedNPComplete.gaussian_schedule_pair_hinge_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:46.865339+00:00
-- url     : https://prove2.me/theorems/795e8196-85dd-4708-baf5-6543fb639bf6
-- title:
--   CSeparated NPComplete: gaussian schedule pair hinge before
-- statement:
--   The CSeparated NPComplete construction uses the gaussian schedule pair hinge before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L137-L158
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L137-L158

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_pair_hinge_before {n : ℕ} {m c : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {i j : ℕ} (hij : i < j) :
    gaussian_pair_hinge c a (gaussian_schedule_class m i) (gaussian_schedule_class m j) =
      c - (m ^ i - m ^ j) ^ 2 * m / dot a (gaussian_schedule_sigma m j) := by sorry
