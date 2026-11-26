-- Prove2me | Theorems.Thm_Auto_aux_spacedSequence_monotone
-- name    : Auto.aux_spacedSequence_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:32.264645+00:00
-- url     : https://prove2.me/theorems/93bedd7f-b4e5-4424-8c76-fd5523b6ee17
-- title:
--   Auto: aux spaced Sequence monotone
-- statement:
--   This auxiliary theorem gives the monotonicity used in the distance estimates below.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L64-L65
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L64-L65

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_spacedSequence_monotone {a : ℤ → ℝ} (ha : SpacedSequence a) : Monotone a := by sorry
