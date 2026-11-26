-- Prove2me | Theorems.Thm_Erdos266_two_le_of_dOf_pos
-- name    : Erdos266.two_le_of_dOf_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:07.239194+00:00
-- url     : https://prove2.me/theorems/0981c83b-461d-5068-ab66-b2f43b6d78f8
-- title:
--   Erdos266: two le of d Of pos
-- statement:
--   The Erdos266 construction uses the two le of d Of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L109-L112
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L109-L112

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.two_le_of_dOf_pos {l : ℕ} (h : 0 < dOf l) : 2 ≤ l := by sorry
