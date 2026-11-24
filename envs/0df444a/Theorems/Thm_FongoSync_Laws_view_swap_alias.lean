-- Prove2me | Theorems.Thm_FongoSync_Laws_view_swap_alias
-- name    : FongoSync.Laws.view_swap_alias
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:50.665629+00:00
-- url     : https://prove2.me/theorems/0fc26093-8507-4069-8eaf-f1e1ea0e13fc
-- title:
--   Laws: view swap alias
-- statement:
--   Swapping an alias with a neighbouring change leaves the view the same.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L166-L169
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L166-L169

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.view_swap_alias (sc : Schema) (pre post : List (Change Value)) (a b : Change Value)
    (h : a.field = ALIAS) :
    view sc (pre ++ a :: b :: post) = view sc (pre ++ b :: a :: post) := by sorry
