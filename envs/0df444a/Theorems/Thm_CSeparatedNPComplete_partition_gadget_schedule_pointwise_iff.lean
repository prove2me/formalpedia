-- Prove2me | Theorems.Thm_CSeparatedNPComplete_partition_gadget_schedule_pointwise_iff
-- name    : CSeparatedNPComplete.partition_gadget_schedule_pointwise_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:38.737809+00:00
-- url     : https://prove2.me/theorems/872d56af-48f6-577c-a19d-85c7a7909319
-- title:
--   CSeparated NPComplete: partition gadget schedule pointwise iff
-- statement:
--   The fixed Gaussian threshold is attained exactly by equal-cardinality
--   partition selectors. Here `d` is the full feature dimension.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionEquivalence.lean#L13-L59
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionEquivalence.lean#L13-L59

module
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
public import Definitions.Def_CSeparatedNPComplete_Gadget
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.partition_gadget_schedule_pointwise_iff
    (d : Nat) (a s : Vec d)
    (hd : 4 ≤ d) (hc : 1 ≤ dot s 1 / 2) (hs : perf_square_vec s) :
    (box_constraints a ∧ dot a 1 = (d : ℝ) / 2 ∧
      hinge_form (dot s 1 / 2) a (partition_gadget_schedule d s) ≤
        partition_schedule_threshold d s) ↔ is_ec_partition a s := by sorry
