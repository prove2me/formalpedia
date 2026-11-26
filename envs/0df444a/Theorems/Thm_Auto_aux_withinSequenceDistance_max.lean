-- Prove2me | Theorems.Thm_Auto_aux_withinSequenceDistance_max
-- name    : Auto.aux_withinSequenceDistance_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:49.75456+00:00
-- url     : https://prove2.me/theorems/8dc73d3b-afc2-5ae2-af6c-e223aceff07f
-- title:
--   Auto: aux within Sequence Distance max
-- statement:
--   Pointwise maxima remain within a common finite sequence-distance comparison.
--   This is used when finite bracket majorants produce the maximum of two nearby
--   scale sequences.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L411-L417
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L411-L417

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_withinSequenceDistance_max {a b c : ℤ → ℝ} {k : ℕ}
    (hab : WithinSequenceDistance a b k) (hac : WithinSequenceDistance a c k) :
    WithinSequenceDistance a (fun j => max (b j) (c j)) k := by sorry
