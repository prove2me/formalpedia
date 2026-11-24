-- Prove2me | Theorems.Thm_FongoSync_not_live_of_deleted
-- name    : FongoSync.not_live_of_deleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:29.709013+00:00
-- url     : https://prove2.me/theorems/dfdc0a7d-6cb7-4930-87e0-99ec7549277a
-- title:
--   Fongo Sync: not live of deleted
-- statement:
--   A deleted entity is never live.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L231-L239
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L231-L239

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.not_live_of_deleted (sc : Schema) (inp : Inputs) (g : Gid)
    (hd : deleted sc inp g) : ¬ Live sc inp g := by sorry
