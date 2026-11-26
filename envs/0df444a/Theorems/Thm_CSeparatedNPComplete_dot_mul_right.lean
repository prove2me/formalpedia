-- Prove2me | Theorems.Thm_CSeparatedNPComplete_dot_mul_right
-- name    : CSeparatedNPComplete.dot_mul_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:51:15.225099+00:00
-- url     : https://prove2.me/theorems/c361ea66-5271-47bd-b881-bb4428ea478d
-- title:
--   CSeparated NPComplete: dot mul right
-- statement:
--   The CSeparated NPComplete construction uses the dot mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L17-L22
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L17-L22

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.dot_mul_right {n : Nat} (a v : Vec n) (r : ℝ) :
    dot a (fun i => r * v i) = r * dot a v := by sorry
