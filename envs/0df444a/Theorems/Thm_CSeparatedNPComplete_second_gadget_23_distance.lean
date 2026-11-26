-- Prove2me | Theorems.Thm_CSeparatedNPComplete_second_gadget_23_distance
-- name    : CSeparatedNPComplete.second_gadget_23_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:48:59.748802+00:00
-- url     : https://prove2.me/theorems/09aaae26-380d-54c3-85ee-13ddd34ec9a9
-- title:
--   CSeparated NPComplete: second gadget 23 distance
-- statement:
--   The CSeparated NPComplete construction uses the second gadget 23 distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L58-L66
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/Gadget.lean#L58-L66

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.second_gadget_23_distance {n : ℕ} (m c : ℝ) (a s : Vec n) :
    dot a (sqVec (second_gadget_mu2 m c s - second_gadget_mu3 m c)) =
      second_gadget_gamma n m * second_gadget_gamma n m *
        dot a (sqVec (fun i => c + m * Real.sqrt (s i))) := by sorry
