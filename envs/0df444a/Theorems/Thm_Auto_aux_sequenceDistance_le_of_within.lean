-- Prove2me | Theorems.Thm_Auto_aux_sequenceDistance_le_of_within
-- name    : Auto.aux_sequenceDistance_le_of_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:23.045105+00:00
-- url     : https://prove2.me/theorems/48f05b4a-6999-4fa9-92a0-cc1be58fb02f
-- title:
--   Auto: aux sequence Distance le of within
-- statement:
--   This auxiliary theorem is useful for deriving all distance estimates from an explicit
--   comparison at a particular integer shift.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L368-L374
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L368-L374

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_sequenceDistance_le_of_within {a b : ℤ → ℝ} {k : ℕ}
    (hk : WithinSequenceDistance a b k) : SequenceDistance a b ≤ (k : WithTop ℕ) := by sorry
