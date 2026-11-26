-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_gamma_pos
-- name    : CSeparatedNPComplete.second_gadget_gamma_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:52:10.204884+00:00
-- url     : https://prove2.me/theorems/84625134-783c-45aa-84f8-8d0e3db86e8d
-- title:
--   CSeparated NPComplete: second gadget gamma pos
-- statement:
--   The CSeparated NPComplete construction uses the second gadget gamma pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L75-L77
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L75-L77

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_gamma_pos (n : Nat) {m : ℝ} (hm : 0 < m) :
    0 < second_gadget_gamma n m := by sorry
