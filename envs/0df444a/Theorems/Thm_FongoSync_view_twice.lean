-- Prove2me | Theorems.Thm_FongoSync_view_twice
-- name    : FongoSync.view_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:30.946208+00:00
-- url     : https://prove2.me/theorems/ab2d2f80-fc19-47a4-9ef8-20a66d044dda
-- title:
--   Fongo Sync: view twice
-- statement:
--   Receiving a change twice in a row leaves the view as receiving it once.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L317-L326
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L317-L326

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.view_twice (sc : Schema) (pre post : List (Change Value)) (a : Change Value) :
    view sc (pre ++ a :: a :: post) = view sc (pre ++ a :: post) := by sorry
