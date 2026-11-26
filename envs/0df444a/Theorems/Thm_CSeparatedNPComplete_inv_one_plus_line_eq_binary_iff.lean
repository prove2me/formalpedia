-- Prove2me | Theorems.Thm_CSeparatedNPComplete_inv_one_plus_line_eq_binary_iff
-- name    : CSeparatedNPComplete.inv_one_plus_line_eq_binary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:14.532628+00:00
-- url     : https://prove2.me/theorems/01f018ba-30e3-4cd2-a719-c714fd13c42e
-- title:
--   CSeparated NPComplete: inv one plus line eq binary iff
-- statement:
--   The chord is attained exactly at the two binary endpoints.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L16-L26
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Reciprocal.lean#L16-L26

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.inv_one_plus_line_eq_binary_iff (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1 + x)⁻¹ = 1 - x / 2 ↔ x = 0 ∨ x = 1 := by sorry
