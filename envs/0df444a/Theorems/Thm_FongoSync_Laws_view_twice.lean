-- Prove2me | Theorems.Thm_FongoSync_Laws_view_twice
-- name    : FongoSync.Laws.view_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:50.548805+00:00
-- url     : https://prove2.me/theorems/83a24fd9-7515-45aa-b169-fb7fce370bbc
-- title:
--   Laws: view twice
-- statement:
--   Receiving a change twice in a row leaves the view as receiving it once.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L172-L174
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L172-L174

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_view_twice

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.view_twice (sc : Schema) (pre post : List (Change Value)) (a : Change Value) :
    view sc (pre ++ a :: a :: post) = view sc (pre ++ a :: post) := by sorry
