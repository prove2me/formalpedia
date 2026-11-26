-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_exists_ec_partition_iff
-- name    : CSeparatedNPComplete.SquareReduction.exists_ec_partition_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:20.623447+00:00
-- url     : https://prove2.me/theorems/be9ce676-35d8-4318-ace2-e7f2736c0eff
-- title:
--   Square Reduction: exists ec partition iff
-- statement:
--   Correctness of the explicit reduction, with no assumptions on a caller's
--   choice of base and no restriction to paired target witnesses.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L222-L256
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L222-L256

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.exists_ec_partition_iff {n : ℕ} (a : Fin n → ℕ) :
    (∃ x : Vec (n + n), is_ec_partition x (values a)) ↔ HasPartition a := by sorry
