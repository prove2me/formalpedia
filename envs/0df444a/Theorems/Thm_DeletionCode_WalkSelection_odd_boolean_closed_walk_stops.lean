-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_odd_boolean_closed_walk_stops
-- name    : DeletionCode.WalkSelection.odd_boolean_closed_walk_stops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:50.671677+00:00
-- url     : https://prove2.me/theorems/f61432be-4dd5-453a-b443-1907ab11ba85
-- title:
--   Walk Selection: odd boolean closed walk stops
-- statement:
--   The stopping dichotomy together with derived independence and generating
--   provenance, using the actual Boolean walk and chronological step indices.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L209-L224
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L209-L224

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.odd_boolean_closed_walk_stops {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j))
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    ∃ (i : Fin m) (S : Finset (Fin m)),
      ScanState (walkStep p) Good i.val S ∧ GeneratingSelected p S ∧
      ¬ SignedMember (walkStep p) S (walkStep p i) ∧
        (walkStep p i ∈ selectedSpan (walkStep p) S ∨
          (walkStep p i ∉ selectedSpan (walkStep p) S ∧
            LinearIndepOn ℚ (walkStep p) ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
            ¬ Good (insert i S) ∧ GeneratingSelected p (insert i S))) := by sorry
