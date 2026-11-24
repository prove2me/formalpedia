-- Prove2me | Theorems.Thm_FongoSync_Full_view_ignores_bad_alias
-- name    : FongoSync.Full.view_ignores_bad_alias
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:28.971545+00:00
-- url     : https://prove2.me/theorems/1fc508cd-1025-4870-a109-8620c79224d6
-- title:
--   Full: view ignores bad alias
-- statement:
--   An alias that does not name another gid is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L459-L461
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L459-L461

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_ignores_bad_alias (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : aliasOk c = false) : view sc (c :: cs) = view sc cs := by sorry
