-- Prove2me | Theorems.Thm_CSeparatedNPComplete_hinge_eq_zero_iff
-- name    : CSeparatedNPComplete.hinge_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:46:43.602691+00:00
-- url     : https://prove2.me/theorems/ea061620-0621-57ab-b731-fcbb2f7396ee
-- title:
--   CSeparated NPComplete: hinge eq zero iff
-- statement:
--   The CSeparated NPComplete construction uses the hinge eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L83-L85
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L83-L85

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.hinge_eq_zero_iff {c D S : ℝ} (hS : 0 < S) :
    hinge c D S = 0 ↔ c * S ≤ D := by sorry
