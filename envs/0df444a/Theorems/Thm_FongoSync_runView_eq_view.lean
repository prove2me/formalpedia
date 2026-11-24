-- Prove2me | Theorems.Thm_FongoSync_runView_eq_view
-- name    : FongoSync.runView_eq_view
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:58.243413+00:00
-- url     : https://prove2.me/theorems/1bc4ac75-1329-4e13-a5af-612a36ec118b
-- title:
--   Fongo Sync: run View eq view
-- statement:
--   **The computed view is the view.**
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L289-L290
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L289-L290

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical

theorem FongoSync.runView_eq_view (sc : Schema) (cs : List (Change Value)) : runView sc cs = view sc cs := by sorry
