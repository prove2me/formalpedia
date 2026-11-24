-- Prove2me | Theorems.Thm_FongoSync_Laws_state_swap
-- name    : FongoSync.Laws.state_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:20.612968+00:00
-- url     : https://prove2.me/theorems/de678cba-3746-43c1-a673-93d912ae01ee
-- title:
--   Laws: state swap
-- statement:
--   Swapping two neighbouring changes anywhere in a delivery, from any state, leaves every
--   register the same, unless they write one register at one clock with different values.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L95-L99
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L95-L99

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.state_swap (σ : String → String → Strategy) (st : State V)
    (pre post : List (Change V)) (a b : Change V) (h : Compatible a b) :
    (pre ++ a :: b :: post).foldl (State.apply σ) st =
      (pre ++ b :: a :: post).foldl (State.apply σ) st := by sorry
