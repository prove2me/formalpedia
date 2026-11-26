-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_hinge_form_iff
-- name    : CSeparatedNPComplete.second_gadget_hinge_form_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:06.752681+00:00
-- url     : https://prove2.me/theorems/05c5ddcf-500f-4454-8b12-b6828326ed14
-- title:
--   CSeparated NPComplete: second gadget hinge form iff
-- statement:
--   The three-Gaussian gadget enforces the partition equality. This version
--   only assumes nonnegative coordinates; the binary perfect-square case follows
--   by specialization.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L166-L197
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L166-L197

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_hinge_form_iff {n : ℕ} (m c : ℝ) (a s : Vec n)
    (hm : 1 ≤ m) (hc : 1 ≤ c) (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 ≤ s i)
    (hcard : dot a 1 = m) :
    hinge_form c a (second_gadget_instance m c s) = 0 ↔ dot a s = c := by sorry
