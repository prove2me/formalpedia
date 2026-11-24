-- Prove2me | Theorems.Thm_FongoSync_Laws_full_view_ignores_unencodable
-- name    : FongoSync.Laws.full_view_ignores_unencodable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:07:03.299466+00:00
-- url     : https://prove2.me/theorems/e6756084-64f2-4d4c-8343-b7c85938ad5b
-- title:
--   Laws: full view ignores unencodable
-- statement:
--   A change whose clock the text form cannot hold is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L197-L200
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L197-L200

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.full_view_ignores_unencodable (sc : Full.Schema) (c : Change Value)
    (cs : List (Change Value)) (h : ¬ c.clock.encodable) :
    Full.view sc (c :: cs) = Full.view sc cs := by sorry
