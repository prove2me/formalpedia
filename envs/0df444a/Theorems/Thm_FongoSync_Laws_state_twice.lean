-- Prove2me | Theorems.Thm_FongoSync_Laws_state_twice
-- name    : FongoSync.Laws.state_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:26.722844+00:00
-- url     : https://prove2.me/theorems/1391a9e5-0b9f-4276-81e1-436a8384c1d9
-- title:
--   Laws: state twice
-- statement:
--   Receiving a change twice in a row anywhere in a delivery is receiving it once.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L102-L106
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L102-L106

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.state_twice (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a : Change V) :
    (pre ++ a :: a :: post).foldl (State.apply σ) st =
      (pre ++ a :: post).foldl (State.apply σ) st := by sorry
