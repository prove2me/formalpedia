-- Prove2me | Theorems.Thm_CSeparatedNPComplete_gaussian_schedule_hinge_form_prefix_m_ge_2
-- name    : CSeparatedNPComplete.gaussian_schedule_hinge_form_prefix_m_ge_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:51.956745+00:00
-- url     : https://prove2.me/theorems/7fc79602-d853-4b3e-b3b5-99e8557eb38d
-- title:
--   CSeparated NPComplete: gaussian schedule hinge form prefix m ge 2
-- statement:
--   The total hinge loss of the schedule, expressed using its coordinate correction.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L204-L217
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Schedule.lean#L204-L217

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_Schedule
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.gaussian_schedule_hinge_form_prefix_m_ge_2 {n : ℕ} (k : ℕ) {m c : ℝ}
    (a : Vec n) (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : is_vec_leq 0 a)
    (hsum : dot a 1 = m) :
    hinge_form c a (gaussian_schedule m (k + 1)) =
      c * (k : ℝ) * ((k : ℝ) + 1) / 2 - gaussian_schedule_hinge_correction a k := by sorry
