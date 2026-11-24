-- Prove2me | Theorems.Thm_FongoSync_Full_view_ignores_unknown_collection
-- name    : FongoSync.Full.view_ignores_unknown_collection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:20.71973+00:00
-- url     : https://prove2.me/theorems/d9e01125-5ddb-416b-9298-9be631ccff7e
-- title:
--   Full: view ignores unknown collection
-- statement:
--   A change to a collection the schema does not declare is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L454-L456
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L454-L456

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_ignores_unknown_collection (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : sc.find c.collection = none) : view sc (c :: cs) = view sc cs := by sorry
