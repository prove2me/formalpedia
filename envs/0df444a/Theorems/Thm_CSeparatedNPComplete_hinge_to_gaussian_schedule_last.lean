-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_to_gaussian_schedule_last
-- name    : CSeparatedNPComplete.hinge_to_gaussian_schedule_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:44.593884+00:00
-- url     : https://prove2.me/theorems/b8eb9fca-247d-4bcb-84f6-8fb816df75ae
-- title:
--   CSeparated NPComplete: hinge to gaussian schedule last
-- statement:
--   The CSeparated NPComplete construction uses the hinge to gaussian schedule last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L165-L201
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L165-L201

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_to_gaussian_schedule_last {n : ℕ} {m c : ℝ} (a : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a) (hsum : dot a 1 = m)
    {j : ℕ} (hj : 0 < j) :
    hinge_to c a (gaussian_schedule m j) (gaussian_schedule_class m j) =
      c * (j : ℝ) - (1 + dot a (canon_e (j - 1)))⁻¹ := by sorry
