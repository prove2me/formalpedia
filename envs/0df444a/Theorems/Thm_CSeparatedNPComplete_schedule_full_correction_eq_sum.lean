-- Prove2me | Theorems.Thm_CSeparatedNPComplete_schedule_full_correction_eq_sum
-- name    : CSeparatedNPComplete.schedule_full_correction_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:15.198624+00:00
-- url     : https://prove2.me/theorems/8605a9b7-33ae-5a6f-aac4-f013be1a7945
-- title:
--   CSeparated NPComplete: schedule full correction eq sum
-- statement:
--   The schedule correction includes every feature coordinate.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L56-L60
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L56-L60

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.schedule_full_correction_eq_sum {n : Nat} (a : Vec n) :
    gaussian_schedule_hinge_correction a n = ∑ i, (1 + a i)⁻¹ := by sorry
