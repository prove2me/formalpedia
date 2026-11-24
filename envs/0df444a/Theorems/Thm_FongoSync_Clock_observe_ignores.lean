-- Prove2me | Theorems.Thm_FongoSync_Clock_observe_ignores
-- name    : FongoSync.Clock.observe_ignores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:47.744718+00:00
-- url     : https://prove2.me/theorems/d83d2824-8d16-4053-a678-3d0703563390
-- title:
--   Clock: observe ignores
-- statement:
--   A reading the text form cannot hold is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L135-L137
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L135-L137

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.observe_ignores (c : Clock) (remote : Hlc) (h : ¬ remote.encodable) :
    c.observe remote = c := by sorry
