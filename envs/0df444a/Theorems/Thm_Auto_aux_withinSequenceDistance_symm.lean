-- Prove2me | Theorems.Thm_Auto_aux_withinSequenceDistance_symm
-- name    : Auto.aux_withinSequenceDistance_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:40:44.030407+00:00
-- url     : https://prove2.me/theorems/c519626c-6d8d-5b5a-989b-62fbf53cc4fc
-- title:
--   Auto: aux within Sequence Distance symm
-- statement:
--   This auxiliary theorem transports a distance comparison after exchanging its two sequences.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L377-L389
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L377-L389

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_withinSequenceDistance_symm {a b : ℤ → ℝ} {k : ℕ} :
    WithinSequenceDistance a b k ↔ WithinSequenceDistance b a k := by sorry
