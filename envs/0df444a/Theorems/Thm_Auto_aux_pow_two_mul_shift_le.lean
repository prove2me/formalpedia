-- Prove2me | Theorems.Thm_Auto_aux_pow_two_mul_shift_le
-- name    : Auto.aux_pow_two_mul_shift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:50.588384+00:00
-- url     : https://prove2.me/theorems/bdb657d6-5148-4309-983c-a22a3a24f8f2
-- title:
--   Auto: aux pow two mul shift le
-- statement:
--   This auxiliary theorem is the backwards form of the iterated spacing inequality.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L85-L87
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L85-L87

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_pow_two_mul_shift_le {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ k * a (j - k) ≤ a j := by sorry
