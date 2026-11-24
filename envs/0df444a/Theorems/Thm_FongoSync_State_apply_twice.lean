-- Prove2me | Theorems.Thm_FongoSync_State_apply_twice
-- name    : FongoSync.State.apply_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:04:00.864808+00:00
-- url     : https://prove2.me/theorems/ec6b0529-3a39-4801-8f79-7bc561cb3641
-- title:
--   State: apply twice
-- statement:
--   Applying a change a second time changes nothing.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L126-L132
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L126-L132

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
import Theorems.Thm_FongoSync_apply_twice

set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.State.apply_twice (σ : String → String → Strategy) (st : State V) (a : Change V) :
    State.apply σ (State.apply σ st a) a = State.apply σ st a := by sorry
