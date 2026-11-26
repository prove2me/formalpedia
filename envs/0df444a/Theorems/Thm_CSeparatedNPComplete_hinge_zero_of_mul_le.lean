-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_zero_of_mul_le
-- name    : CSeparatedNPComplete.hinge_zero_of_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:52:14.78923+00:00
-- url     : https://prove2.me/theorems/2921a65b-a293-5455-8747-65382d6ad068
-- title:
--   CSeparated NPComplete: hinge zero of mul le
-- statement:
--   The CSeparated NPComplete construction uses the hinge zero of mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L90-L91
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L90-L91

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_zero_of_mul_le {c D S : ℝ} (hS : 0 < S)
    (h : c * S ≤ D) : hinge c D S = 0 := by sorry
