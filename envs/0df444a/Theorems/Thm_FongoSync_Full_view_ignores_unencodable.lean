-- Prove2me | Theorems.Thm_FongoSync_Full_view_ignores_unencodable
-- name    : FongoSync.Full.view_ignores_unencodable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:23.158412+00:00
-- url     : https://prove2.me/theorems/886519dc-36ee-42f5-9842-6233dd279a1d
-- title:
--   Full: view ignores unencodable
-- statement:
--   A change whose clock the text form cannot hold is ignored.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L449-L451
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L449-L451

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_ignores_unencodable (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : ¬ c.clock.encodable) : view sc (c :: cs) = view sc cs := by sorry
