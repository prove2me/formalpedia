-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_odd_closed_walk_stops
-- name    : DeletionCode.WalkSelection.odd_closed_walk_stops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:13.388444+00:00
-- url     : https://prove2.me/theorems/6ca0d4e7-bd34-4efd-84df-a13b45b43e60
-- title:
--   Walk Selection: odd closed walk stops
-- statement:
--   An odd closed walk must trigger one of the two actual scan stopping cases.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L128-L143
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L128-L143

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.odd_closed_walk_stops (p : Fin (m + 1) → V)
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    Stopped (walkStep p) Good := by sorry
