-- Prove2me | Theorems.Thm_CSeparatedNPComplete_full_correction_le_line
-- name    : CSeparatedNPComplete.full_correction_le_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:07.545742+00:00
-- url     : https://prove2.me/theorems/37e590b4-ec2b-5dd8-9faf-c242e34b9165
-- title:
--   CSeparated NPComplete: full correction le line
-- statement:
--   The CSeparated NPComplete construction uses the full correction le line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L32-L35
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L32-L35

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.full_correction_le_line {n : Nat} (a : Vec n) (ha : box_constraints a) :
    (∑ i, (1 + a i)⁻¹) ≤ (n : ℝ) - dot a 1 / 2 := by sorry
