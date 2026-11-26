-- Prove2me | Theorems.Thm_CSeparatedNPComplete_partition_schedule_threshold_quarter_integral
-- name    : CSeparatedNPComplete.partition_schedule_threshold_quarter_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:56.663+00:00
-- url     : https://prove2.me/theorems/cc68f00b-1d11-4989-b5b1-4ca066478966
-- title:
--   CSeparated NPComplete: partition schedule threshold quarter integral
-- statement:
--   For natural input weights, the fixed threshold is an integer multiple of `1/4`.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionEquivalence.lean#L62-L67
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/PartitionEquivalence.lean#L62-L67

module
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
public import Definitions.Def_CSeparatedNPComplete_Gadget
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.partition_schedule_threshold_quarter_integral (d : Nat) (s : Fin d → Nat) :
    ∃ z : ℤ, partition_schedule_threshold d (fun i => (s i : ℝ)) = (z : ℝ) / 4 := by sorry
