-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_12_distance
-- name    : CSeparatedNPComplete.second_gadget_12_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:51.054713+00:00
-- url     : https://prove2.me/theorems/bf77e8a8-7305-55c4-acaa-e2177a4dbca9
-- title:
--   CSeparated NPComplete: second gadget 12 distance
-- statement:
--   The CSeparated NPComplete construction uses the second gadget 12 distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L38-L46
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L38-L46

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_12_distance {n : ℕ} (m c : ℝ) (a s : Vec n) :
    dot a (sqVec (second_gadget_mu1 m c - second_gadget_mu2 m c s)) =
      second_gadget_gamma n m * second_gadget_gamma n m *
        m * m * dot a (sqVec (fun i => Real.sqrt (s i))) := by sorry
