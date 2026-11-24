-- Prove2me | Theorems.Thm_FongoSync_State_apply_swap
-- name    : FongoSync.State.apply_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:18.440091+00:00
-- url     : https://prove2.me/theorems/bce69c4a-fe1c-4e56-bcdd-1bab9b6cd169
-- title:
--   State: apply swap
-- statement:
--   Two compatible changes may be applied in either order, to any state.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L102-L123
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L102-L123

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.State.apply_swap (σ : String → String → Strategy) (st : State V) (a b : Change V)
    (h : Compatible a b) :
    State.apply σ (State.apply σ st a) b = State.apply σ (State.apply σ st b) a := by sorry
