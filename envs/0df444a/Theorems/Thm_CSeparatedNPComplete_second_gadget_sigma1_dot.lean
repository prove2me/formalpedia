-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_sigma1_dot
-- name    : CSeparatedNPComplete.second_gadget_sigma1_dot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:48.579686+00:00
-- url     : https://prove2.me/theorems/8a57fa1c-7962-51f9-80a9-cd0e662ded78
-- title:
--   CSeparated NPComplete: second gadget sigma1 dot
-- statement:
--   The CSeparated NPComplete construction uses the second gadget sigma1 dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L11-L18
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L11-L18

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_sigma1_dot {n : ℕ} (m : ℝ) (a : Vec n) :
    dot a (second_gadget_sigma1 m) =
      second_gadget_gamma n m * second_gadget_gamma n m * dot a 1 := by sorry
