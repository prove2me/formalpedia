-- Prove2me | Theorems.Thm_FongoSync_State_foldl_swap
-- name    : FongoSync.State.foldl_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:31.14269+00:00
-- url     : https://prove2.me/theorems/909274bd-6dfe-45b9-ae49-fd15f5e6a024
-- title:
--   State: foldl swap
-- statement:
--   Swapping two neighbouring compatible changes anywhere in a delivery, from any state, leaves
--   every register the same.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L136-L140
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L136-L140

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.State.foldl_swap (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a b : Change V) (h : Compatible a b) :
    (pre ++ a :: b :: post).foldl (State.apply σ) st =
      (pre ++ b :: a :: post).foldl (State.apply σ) st := by sorry
