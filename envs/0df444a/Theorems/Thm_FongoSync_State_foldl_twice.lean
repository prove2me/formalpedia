-- Prove2me | Theorems.Thm_FongoSync_State_foldl_twice
-- name    : FongoSync.State.foldl_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:33.53363+00:00
-- url     : https://prove2.me/theorems/811cef43-e038-4376-9e87-54f5ae6607b3
-- title:
--   State: foldl twice
-- statement:
--   Receiving a change twice in a row anywhere in a delivery is receiving it once.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L143-L147
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L143-L147

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.State.foldl_twice (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a : Change V) :
    (pre ++ a :: a :: post).foldl (State.apply σ) st =
      (pre ++ a :: post).foldl (State.apply σ) st := by sorry
