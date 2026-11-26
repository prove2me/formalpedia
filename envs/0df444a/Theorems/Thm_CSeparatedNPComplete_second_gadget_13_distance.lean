-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_13_distance
-- name    : CSeparatedNPComplete.second_gadget_13_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:57.426801+00:00
-- url     : https://prove2.me/theorems/042bdc47-6bde-590e-82fd-1c07e698baa6
-- title:
--   CSeparated NPComplete: second gadget 13 distance
-- statement:
--   The CSeparated NPComplete construction uses the second gadget 13 distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L48-L56
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L48-L56

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_13_distance {n : ℕ} (m c : ℝ) (a : Vec n) :
    dot a (sqVec (second_gadget_mu1 m c - second_gadget_mu3 m c)) =
      second_gadget_gamma n m * second_gadget_gamma n m * c * c * dot a 1 := by sorry
