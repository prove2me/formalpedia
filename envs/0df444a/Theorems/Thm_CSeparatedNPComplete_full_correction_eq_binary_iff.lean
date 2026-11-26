-- Prove2me | Theorems.Thm_CSeparatedNPComplete_full_correction_eq_binary_iff
-- name    : CSeparatedNPComplete.full_correction_eq_binary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:14.207792+00:00
-- url     : https://prove2.me/theorems/56527a8d-183d-4a62-862a-3d9e968d3122
-- title:
--   CSeparated NPComplete: full correction eq binary iff
-- statement:
--   The CSeparated NPComplete construction uses the full correction eq binary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L37-L53
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L37-L53

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.full_correction_eq_binary_iff {n : Nat} (a : Vec n) (ha : box_constraints a) :
    (∑ i, (1 + a i)⁻¹) = (n : ℝ) - dot a 1 / 2 ↔ is_binary a := by sorry
