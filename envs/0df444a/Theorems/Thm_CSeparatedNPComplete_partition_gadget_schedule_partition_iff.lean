-- Prove2me | Theorems.Thm_CSeparatedNPComplete_partition_gadget_schedule_partition_iff
-- name    : CSeparatedNPComplete.partition_gadget_schedule_partition_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:57:53.547217+00:00
-- url     : https://prove2.me/theorems/801e6b05-dccd-42f3-b059-82be8aa83144
-- title:
--   CSeparated NPComplete: partition gadget schedule partition iff
-- statement:
--   The explicit Gaussian construction satisfies its threshold constraint exactly
--   for equal-cardinality partition selectors. This is the main submission result.
--
--   For `d ≥ 4` perfect-square entries with half-total at least one, the
--   left side allows every selector in the unit cube with total weight `d/2`. The
--   inequality forces binary coordinates and the partition balance.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/Solution.lean#L83-L89
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/Solution.lean#L83-L89

module
public import Definitions.Def_CSeparatedNPComplete
public import Definitions.Def_CSeparatedNPComplete_Solution
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.partition_gadget_schedule_partition_iff
    (d : Nat) (a s : Vec d)
    (hd : 4 ≤ d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d s) ↔ is_ec_partition a s := by sorry
