-- Prove2me | Theorems.Thm_FongoSync_Laws_full_view_ignores_bad_alias
-- name    : FongoSync.Laws.full_view_ignores_bad_alias
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:07:05.955781+00:00
-- url     : https://prove2.me/theorems/562fc146-2c99-4045-bfbd-8f434d1d781d
-- title:
--   Laws: full view ignores bad alias
-- statement:
--   An alias that does not name another gid is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L209-L212
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L209-L212

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.full_view_ignores_bad_alias (sc : Full.Schema) (c : Change Value)
    (cs : List (Change Value)) (h : aliasOk c = false) :
    Full.view sc (c :: cs) = Full.view sc cs := by sorry
