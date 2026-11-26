-- Prove2me | Theorems.Thm_CSeparatedNPComplete_inv_one_plus_le_line
-- name    : CSeparatedNPComplete.inv_one_plus_le_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:19.774805+00:00
-- url     : https://prove2.me/theorems/8333eaa2-4057-40b5-b890-107eb7a930e7
-- title:
--   CSeparated NPComplete: inv one plus le line
-- statement:
--   The chord bound for the reciprocal potential on the unit interval.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L10-L13
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L10-L13

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.inv_one_plus_le_line (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1 + x)⁻¹ ≤ 1 - x / 2 := by sorry
