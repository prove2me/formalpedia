-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_against_nonneg
-- name    : CSeparatedNPComplete.hinge_against_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:09.496856+00:00
-- url     : https://prove2.me/theorems/36646bd3-1c2b-46f3-aad6-f6fc2ffc44b8
-- title:
--   CSeparated NPComplete: hinge against nonneg
-- statement:
--   The CSeparated NPComplete construction uses the hinge against nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L96-L100
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L96-L100

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_against_nonneg {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L : List (Gaussian n)) : 0 ≤ hinge_against c a g L := by sorry
