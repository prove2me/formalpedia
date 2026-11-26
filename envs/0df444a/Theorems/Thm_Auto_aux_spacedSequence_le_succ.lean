-- Prove2me | Theorems.Thm_Auto_aux_spacedSequence_le_succ
-- name    : Auto.aux_spacedSequence_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:22.540039+00:00
-- url     : https://prove2.me/theorems/d3859aa9-26f8-4725-af9b-1fa94d33ea0d
-- title:
--   Auto: aux spaced Sequence le succ
-- statement:
--   This auxiliary theorem records the one-step monotonicity implied by multiplicative spacing.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L57-L61
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L57-L61

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_spacedSequence_le_succ {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) :
    a j ≤ a (j + 1) := by sorry
