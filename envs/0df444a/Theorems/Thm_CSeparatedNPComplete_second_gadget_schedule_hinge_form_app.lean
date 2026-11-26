-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_schedule_hinge_form_app
-- name    : CSeparatedNPComplete.second_gadget_schedule_hinge_form_app
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:47.653228+00:00
-- url     : https://prove2.me/theorems/9f87740b-c02a-54ba-bd13-8dfdfc7b9e0f
-- title:
--   CSeparated NPComplete: second gadget schedule hinge form app
-- statement:
--   The shifted three-Gaussian gadget has no hinge contribution across the schedule.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/CrossGadget.lean#L208-L224
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/CrossGadget.lean#L208-L224

module
public import Definitions.Def_CSeparatedNPComplete_Schedule
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_schedule_hinge_form_app {n : ℕ} (m c : ℝ) (a s : Vec n)
    (hm : 2 ≤ m) (hc : 1 ≤ c) (ha : box_constraints a) (hs : is_vec_leq 0 s)
    (hsum : dot a 1 = m) (hstotal : dot s 1 = 2 * c) (hn : 0 < n) :
    hinge_form c a (second_gadget_instance m c s ++ gaussian_schedule m (n + 1)) =
      hinge_form c a (second_gadget_instance m c s) +
        hinge_form c a (gaussian_schedule m (n + 1)) := by sorry
