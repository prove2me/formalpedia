-- Prove2me | Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating_after_append
-- name    : DeletionCode.WalkSelection.ScanState.generating_after_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:24.813093+00:00
-- url     : https://prove2.me/theorems/4ff59704-2d1c-4968-a6d2-d69071ee3244
-- title:
--   Scan State: generating after append
-- statement:
--   A bad independent append is still generating; the cutoff is irrelevant
--   to the Boolean provenance argument.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L197-L205
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WalkSelection.lean#L197-L205

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}

theorem DeletionCode.WalkSelection.ScanState.generating_after_append {H : Type*} {p : Fin (m + 1) → H → ℚ}
    {Good : Finset (Fin m) → Prop} {n : ℕ} {S : Finset (Fin m)}
    (hs : ScanState (walkStep p) Good n S)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j))
    (i : Fin m) (hi : i.val = n) (hout : walkStep p i ∉ selectedSpan (walkStep p) S) :
    GeneratingSelected p (insert i S) := by sorry
