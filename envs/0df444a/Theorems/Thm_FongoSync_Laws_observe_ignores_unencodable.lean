-- Prove2me | Theorems.Thm_FongoSync_Laws_observe_ignores_unencodable
-- name    : FongoSync.Laws.observe_ignores_unencodable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:32.975136+00:00
-- url     : https://prove2.me/theorems/9605d628-b5b4-487b-8b25-1e62718602b4
-- title:
--   Laws: observe ignores unencodable
-- statement:
--   Observing a reading the text form cannot hold changes nothing.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L26-L28
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L26-L28

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.observe_ignores_unencodable (c : Clock) (remote : Hlc) (h : ¬ remote.encodable) :
    c.observe remote = c := by sorry
