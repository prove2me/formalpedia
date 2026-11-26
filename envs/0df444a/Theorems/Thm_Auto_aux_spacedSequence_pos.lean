-- Prove2me | Theorems.Thm_Auto_aux_spacedSequence_pos
-- name    : Auto.aux_spacedSequence_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:47.763415+00:00
-- url     : https://prove2.me/theorems/ba4c9bad-ca2f-44ec-bfda-0b943403dd50
-- title:
--   Auto: aux spaced Sequence pos
-- statement:
--   This auxiliary theorem extracts positivity from the defining conditions of a spaced sequence.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L53-L54
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L53-L54

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_spacedSequence_pos {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) : 0 < a j := by sorry
