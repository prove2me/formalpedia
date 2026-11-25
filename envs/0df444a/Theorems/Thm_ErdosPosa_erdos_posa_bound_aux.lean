-- Prove2me | Theorems.Thm_ErdosPosa_erdos_posa_bound_aux
-- name    : ErdosPosa.erdos_posa_bound_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:30:55.628708+00:00
-- url     : https://prove2.me/theorems/0cd64c3f-7eac-52e6-9311-d70e67698a57
-- title:
--   Erdos Posa: erdos posa bound aux
-- statement:
--   The Erdős–Pósa dichotomy with the explicit bound `65 (k + 1) (log₂ (k + 1) + 1)`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L45-L58
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/ErdosPosa.lean#L45-L58

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMain
public import Definitions.Def_ErdosPosaLib_ErdosPosa
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
universe u

theorem ErdosPosa.erdos_posa_bound_aux (k : ℕ) {V : Type u} [Finite V] (G : SimpleGraph V) :
    HasDisjointCycles G k ∨
      ∃ X : Set V, X.ncard ≤ 65 * (k + 1) * (Nat.log 2 (k + 1) + 1) ∧ IsFeedbackSet G X := by sorry
