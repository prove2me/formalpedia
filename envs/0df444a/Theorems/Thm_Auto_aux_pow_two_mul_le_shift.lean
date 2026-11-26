-- Prove2me | Theorems.Thm_Auto_aux_pow_two_mul_le_shift
-- name    : Auto.aux_pow_two_mul_le_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:25.0418+00:00
-- url     : https://prove2.me/theorems/53bce869-4b88-4cd9-b6e5-f8669ea28515
-- title:
--   Auto: aux pow two mul le shift
-- statement:
--   This auxiliary theorem iterates the defining spacing inequality forward.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L68-L82
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L68-L82

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_pow_two_mul_le_shift {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ k * a j ≤ a (j + k) := by sorry
