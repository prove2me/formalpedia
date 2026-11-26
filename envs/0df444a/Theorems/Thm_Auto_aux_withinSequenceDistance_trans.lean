-- Prove2me | Theorems.Thm_Auto_aux_withinSequenceDistance_trans
-- name    : Auto.aux_withinSequenceDistance_trans
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:40:48.658515+00:00
-- url     : https://prove2.me/theorems/6a7e46f1-05d8-5ab8-aed2-f10d9b8ec205
-- title:
--   Auto: aux within Sequence Distance trans
-- statement:
--   This auxiliary theorem composes the pointwise comparisons used to define sequence distance.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L392-L404
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L392-L404

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.aux_withinSequenceDistance_trans {a b c : ℤ → ℝ} {k l : ℕ}
    (hab : WithinSequenceDistance a b k) (hbc : WithinSequenceDistance b c l) :
    WithinSequenceDistance a c (k + l) := by sorry
