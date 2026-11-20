-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating
-- name    : DeletionCode.WalkSelection.ScanState.generating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:10:15.109808+00:00
-- url     : https://prove2.me/theorems/726d908d-7e6b-46b1-98d3-0232ecce23f0
-- title:
--   Scan State: generating
-- statement:
--   Boolean endpoints and the causal scan invariant derive generation.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L167-L193
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L167-L193

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.ScanState.generating {H : Type*} {p : Fin (m + 1) → H → ℚ}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep p) Good n S)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j)) : GeneratingSelected p S := by sorry
