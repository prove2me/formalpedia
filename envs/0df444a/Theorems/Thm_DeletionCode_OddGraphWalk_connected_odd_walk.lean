-- Prove2me | Theorems.Thm_DeletionCode_OddGraphWalk_connected_odd_walk
-- name    : DeletionCode.OddGraphWalk.connected_odd_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:20.007379+00:00
-- url     : https://prove2.me/theorems/e2db720a-a9d7-4637-861e-1f9794e7fd3c
-- title:
--   Odd Graph Walk: connected odd walk
-- statement:
--   Finite-index form for a non-two-colorable connected graph.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L66-L72
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L66-L72

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}

theorem DeletionCode.OddGraphWalk.connected_odd_walk (hconnected : G.Connected)
    (hnot : ¬ G.Colorable 2) (x : V) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by sorry
