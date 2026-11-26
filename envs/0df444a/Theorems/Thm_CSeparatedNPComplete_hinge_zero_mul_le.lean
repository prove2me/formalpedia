-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_zero_mul_le
-- name    : CSeparatedNPComplete.hinge_zero_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:52:14.896586+00:00
-- url     : https://prove2.me/theorems/4495f2ae-ec2c-4ee0-aaa0-bf647be77005
-- title:
--   CSeparated NPComplete: hinge zero mul le
-- statement:
--   The CSeparated NPComplete construction uses the hinge zero mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L87-L88
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L87-L88

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_zero_mul_le {c D S : ℝ} (hS : 0 < S)
    (h : hinge c D S = 0) : c * S ≤ D := by sorry
