-- Prove2me | Theorems.Thm_FongoSync_Full_view_dup
-- name    : FongoSync.Full.view_dup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:34.029341+00:00
-- url     : https://prove2.me/theorems/f35e958f-5669-4ecc-8fca-c02f06d1503f
-- title:
--   Full: view dup
-- statement:
--   The Full construction uses the view dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L425-L428
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L425-L428

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_view_dup

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_dup (sc : Schema) (cs : List (Change Value)) (unique : ClockDetermines cs) :
    view sc (cs ++ cs) = view sc cs := by sorry
