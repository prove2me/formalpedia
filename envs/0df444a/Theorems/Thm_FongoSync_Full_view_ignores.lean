-- Prove2me | Theorems.Thm_FongoSync_Full_view_ignores
-- name    : FongoSync.Full.view_ignores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:05.534956+00:00
-- url     : https://prove2.me/theorems/f7914b03-854f-435e-8adf-9901acf7190e
-- title:
--   Full: view ignores
-- statement:
--   A change that is not a candidate does not change the view.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L433-L446
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L433-L446

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_ignores (sc : Schema) (c : Change Value) (cs : List (Change Value))
    (h : ¬ (c.clock.encodable ∧ aliasOk c = true ∧ (sc.find c.collection).isSome)) :
    view sc (c :: cs) = view sc cs := by sorry
