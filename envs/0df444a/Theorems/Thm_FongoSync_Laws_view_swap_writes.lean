-- Prove2me | Theorems.Thm_FongoSync_Laws_view_swap_writes
-- name    : FongoSync.Laws.view_swap_writes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:48.222779+00:00
-- url     : https://prove2.me/theorems/1a34480e-6f2e-4d77-8c9b-a1469ab64028
-- title:
--   Laws: view swap writes
-- statement:
--   Swapping two neighbouring changes leaves the view the same, unless they write one register at
--   one clock with different values.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L160-L163
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L160-L163

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.view_swap_writes (sc : Schema) (pre post : List (Change Value)) (a b : Change Value)
    (h : Compatible a b) :
    view sc (pre ++ a :: b :: post) = view sc (pre ++ b :: a :: post) := by sorry
