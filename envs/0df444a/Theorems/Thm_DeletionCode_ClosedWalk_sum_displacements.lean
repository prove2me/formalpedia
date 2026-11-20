-- Prove2me | Theorems.Thm_DeletionCode_ClosedWalk_sum_displacements
-- name    : DeletionCode.ClosedWalk.sum_displacements
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:03.276308+00:00
-- url     : https://prove2.me/theorems/d6ddce67-a06d-4f51-b232-df261f3d02d5
-- title:
--   Closed Walk: sum displacements
-- statement:
--   Successive displacements telescope, including both endpoints.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ClosedWalk.lean#L16-L28
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ClosedWalk.lean#L16-L28

import Definitions.Def_DeletionCode_WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Definitions.Def_DeletionCode_ClosedWalk
set_option autoImplicit true
open DeletionCode DeletionCode.ClosedWalk
open scoped BigOperators

theorem DeletionCode.ClosedWalk.sum_displacements {V : Type*} [AddCommGroup V] {m : ℕ}
    (p : Fin (m + 1) → V) :
    (∑ i : Fin m, (p i.succ - p i.castSucc)) = p (Fin.last m) - p 0 := by sorry
