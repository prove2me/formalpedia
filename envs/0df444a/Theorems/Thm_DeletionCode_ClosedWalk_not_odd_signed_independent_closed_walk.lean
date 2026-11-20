-- Prove2me | Theorems.Thm_DeletionCode_ClosedWalk_not_odd_signed_independent_closed_walk
-- name    : DeletionCode.ClosedWalk.not_odd_signed_independent_closed_walk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:17.927485+00:00
-- url     : https://prove2.me/theorems/cdb5d1f7-3e07-4f2a-9139-065f940442cc
-- title:
--   Closed Walk: not odd signed independent closed walk
-- statement:
--   In particular, an odd closed walk must use a step outside ±G.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ClosedWalk.lean#L55-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ClosedWalk.lean#L55-L64

import Definitions.Def_DeletionCode_WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Definitions.Def_DeletionCode_ClosedWalk
set_option autoImplicit true
open DeletionCode DeletionCode.ClosedWalk
open scoped BigOperators

theorem DeletionCode.ClosedWalk.not_odd_signed_independent_closed_walk {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (G : I → V) (hG : LinearIndependent ℚ G) (p : Fin (m + 1) → V)
    (label : Fin m → I) (hclosed : p 0 = p (Fin.last m))
    (hsteps : ∀ i : Fin m,
      p i.succ - p i.castSucc = G (label i) ∨
      p i.succ - p i.castSucc = -G (label i)) : ¬ Odd m := by sorry
