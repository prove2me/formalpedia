-- Prove2me | Theorems.Thm_CSeparatedNPComplete_is_binary_box_constraints
-- name    : CSeparatedNPComplete.is_binary_box_constraints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:45.476727+00:00
-- url     : https://prove2.me/theorems/76082c96-b4b1-4004-84bb-007c21d63d03
-- title:
--   CSeparated NPComplete: is binary box constraints
-- statement:
--   The CSeparated NPComplete construction uses the is binary box constraints property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L60-L62
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L60-L62

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.is_binary_box_constraints {n : Nat} {a : Vec n}
    (ha : is_binary a) : box_constraints a := by sorry
