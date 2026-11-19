-- Prove2me | Theorems.Thm_DeletionCode_OddGraphWalk_exists_odd_loop
-- name    : DeletionCode.OddGraphWalk.exists_odd_loop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:27:30.986465+00:00
-- url     : https://prove2.me/theorems/1b327c7c-aacd-46d0-a1fa-8cc9917005e1
-- title:
--   Odd Graph Walk: exists odd loop
-- statement:
--   Negating mathlib's closed-walk characterization of two-colorability gives
--   an odd loop, initially without any constraint on its base vertex.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L17-L24
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L17-L24

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}

theorem DeletionCode.OddGraphWalk.exists_odd_loop (hnot : ¬ G.Colorable 2) :
    ∃ u : V, ∃ q : G.Walk u u, Odd q.length := by sorry
