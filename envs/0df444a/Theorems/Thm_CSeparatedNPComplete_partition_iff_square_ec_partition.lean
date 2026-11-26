-- Prove2me | Theorems.Thm_CSeparatedNPComplete_partition_iff_square_ec_partition
-- name    : CSeparatedNPComplete.partition_iff_square_ec_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:57:50.678469+00:00
-- url     : https://prove2.me/theorems/0cd434b6-6132-5092-b0de-a3de4d54745f
-- title:
--   CSeparated NPComplete: partition iff square ec partition
-- statement:
--   Ordinary PARTITION reduces to equal-cardinality partition of positive
--   perfect squares. The construction chooses its own base, so there are no `hK`
--   or `hbound` assumptions. The target existential ranges over every selector.
--
--   For positive integer inputs, the encoding is a polynomial-time injective
--   many-one reduction; see `SQUARE_PARTITION.md` for the complexity argument and
--   `SquareReduction.encode_bound`, `base_bound`, and `encode_injective` for the
--   formal arithmetic and injectivity results.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/Solution.lean#L72-L75
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/Solution.lean#L72-L75

module
public import Definitions.Def_CSeparatedNPComplete
public import Definitions.Def_CSeparatedNPComplete_Solution
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.partition_iff_square_ec_partition (n : ℕ) (a : Fin n → ℕ) :
    SquareReduction.HasPartition a ↔
      ∃ x : Vec (n + n), is_ec_partition x (SquareReduction.values a) := by sorry
