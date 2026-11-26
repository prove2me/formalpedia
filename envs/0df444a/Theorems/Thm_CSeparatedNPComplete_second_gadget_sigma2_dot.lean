-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_sigma2_dot
-- name    : CSeparatedNPComplete.second_gadget_sigma2_dot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:49.151422+00:00
-- url     : https://prove2.me/theorems/c8b7f9bb-51e9-5ce3-a87f-2233ffcd4bcc
-- title:
--   CSeparated NPComplete: second gadget sigma2 dot
-- statement:
--   The CSeparated NPComplete construction uses the second gadget sigma2 dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L20-L27
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L20-L27

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_sigma2_dot {n : ℕ} (m : ℝ) (a : Vec n) :
    dot a (second_gadget_sigma2 m) =
      second_gadget_gamma n m * second_gadget_gamma n m * m * dot a 1 := by sorry
