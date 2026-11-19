-- Prove2me | Theorems.Thm_DeletionCode_OddGraphWalk_exists_odd_loop_at
-- name    : DeletionCode.OddGraphWalk.exists_odd_loop_at
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:02:12.760289+00:00
-- url     : https://prove2.me/theorems/5ba0b4e6-4376-4c94-a473-933bf906d559
-- title:
--   Odd Graph Walk: exists odd loop at
-- statement:
--   Travelling to an odd loop and returning along the reverse connecting walk
--   changes its length by an even number.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L28-L38
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L28-L38

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}

theorem DeletionCode.OddGraphWalk.exists_odd_loop_at (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ q : G.Walk x x, Odd q.length := by sorry
