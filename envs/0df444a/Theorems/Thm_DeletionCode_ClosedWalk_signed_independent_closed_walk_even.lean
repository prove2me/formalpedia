-- Prove2me | Theorems.Thm_DeletionCode_ClosedWalk_signed_independent_closed_walk_even
-- name    : DeletionCode.ClosedWalk.signed_independent_closed_walk_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:16.024855+00:00
-- url     : https://prove2.me/theorems/c7ed4cd5-1101-439d-9633-fa8ee592a851
-- title:
--   Closed Walk: signed independent closed walk even
-- statement:
--   A closed walk using only signed independent generators has even length.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ClosedWalk.lean#L31-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ClosedWalk.lean#L31-L52

import Definitions.Def_DeletionCode_WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Definitions.Def_DeletionCode_ClosedWalk
set_option autoImplicit true
open DeletionCode DeletionCode.ClosedWalk
open scoped BigOperators

theorem DeletionCode.ClosedWalk.signed_independent_closed_walk_even {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (G : I → V) (hG : LinearIndependent ℚ G) (p : Fin (m + 1) → V)
    (label : Fin m → I) (hclosed : p 0 = p (Fin.last m))
    (hsteps : ∀ i : Fin m,
      p i.succ - p i.castSucc = G (label i) ∨
      p i.succ - p i.castSucc = -G (label i)) : Even m := by sorry
