-- Prove2me | Theorems.Thm_DeletionCode_OddGraphWalk_indexed_of_odd_loop
-- name    : DeletionCode.OddGraphWalk.indexed_of_odd_loop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:02:13.272142+00:00
-- url     : https://prove2.me/theorems/870cd934-d635-42bd-921b-73a071b6d317
-- title:
--   Odd Graph Walk: indexed of odd loop
-- statement:
--   A walk supplies its own finite vertex sequence: no enumeration or edge
--   realization assumption is added when converting to the scan interface.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L55-L63
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/OddGraphWalk.lean#L55-L63

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OddGraphWalk
set_option autoImplicit true
open DeletionCode DeletionCode.OddGraphWalk
variable {V : Type*} {G : SimpleGraph V}

theorem DeletionCode.OddGraphWalk.indexed_of_odd_loop {x : V} (q : G.Walk x x) (hq : Odd q.length) :
    ∃ m : ℕ, Odd m ∧ ∃ vertices : Fin (m + 1) → V,
      vertices 0 = x ∧ vertices (Fin.last m) = x ∧
        ∀ i : Fin m, G.Adj (vertices i.castSucc) (vertices i.succ) := by sorry
