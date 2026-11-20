-- Prove2me | Theorems.Thm_DeletionCode_OddGraphWalk_component_exists_odd_loop_at
-- name    : DeletionCode.OddGraphWalk.component_exists_odd_loop_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:47.710964+00:00
-- url     : https://prove2.me/theorems/c6688962-00ae-4bc7-80b6-dc84e8f1f49f
-- title:
--   Odd Graph Walk: component exists odd loop at
-- statement:
--   The odd loop can be based at the actual ambient vertex `x`, when only its
--   own induced connected component is known to be non-two-colorable.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L42-L51
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L42-L51

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}

theorem DeletionCode.OddGraphWalk.component_exists_odd_loop_at (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ q : G.Walk x x, Odd q.length := by sorry
