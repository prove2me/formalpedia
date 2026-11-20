-- Prove2me | Theorems.Thm_DeletionCode_OddGraphWalk_component_odd_walk
-- name    : DeletionCode.OddGraphWalk.component_odd_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:27:51.943455+00:00
-- url     : https://prove2.me/theorems/2e7d3c27-6b45-4766-aa02-36ec4c99e4a1
-- title:
--   Odd Graph Walk: component odd walk
-- statement:
--   Finite-index form based at `x`, assuming only that the component containing
--   `x` is non-two-colorable. Other components impose no hypotheses.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L76-L82
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L76-L82

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}

theorem DeletionCode.OddGraphWalk.component_odd_walk (x : V)
    (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by sorry
