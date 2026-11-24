-- Prove2me | Theorems.Thm_FongoSync_Laws_full_view_ignores_unknown_collection
-- name    : FongoSync.Laws.full_view_ignores_unknown_collection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:07:03.531355+00:00
-- url     : https://prove2.me/theorems/b0af00d8-b0c7-4443-a3bc-08345f83acd1
-- title:
--   Laws: full view ignores unknown collection
-- statement:
--   A change to a collection the schema does not declare is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L203-L206
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L203-L206

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.full_view_ignores_unknown_collection (sc : Full.Schema) (c : Change Value)
    (cs : List (Change Value)) (h : sc.find c.collection = none) :
    Full.view sc (c :: cs) = Full.view sc cs := by sorry
