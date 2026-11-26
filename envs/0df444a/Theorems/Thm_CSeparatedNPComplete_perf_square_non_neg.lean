-- Prove2me | Theorems.Thm_CSeparatedNPComplete_perf_square_non_neg
-- name    : CSeparatedNPComplete.perf_square_non_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:57.711018+00:00
-- url     : https://prove2.me/theorems/eee1e0e2-d256-4760-9ae9-a37a9111b916
-- title:
--   CSeparated NPComplete: perf square non neg
-- statement:
--   The CSeparated NPComplete construction uses the perf square non neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L64-L69
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionBasic.lean#L64-L69

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.perf_square_non_neg {n : Nat} {s : Vec n}
    (hs : perf_square_vec s) : is_vec_leq 0 s := by sorry
