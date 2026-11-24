-- Prove2me | Theorems.Thm_FongoSync_view_dup
-- name    : FongoSync.view_dup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:04.163641+00:00
-- url     : https://prove2.me/theorems/4db7d8e2-25e4-46bb-933a-f4e2bd4d3d24
-- title:
--   Fongo Sync: view dup
-- statement:
--   The Fongo Sync construction uses the view dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L345-L348
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L345-L348

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.view_dup (sc : Schema) (cs : List (Change Value)) (unique : ClockDetermines cs) :
    view sc (cs ++ cs) = view sc cs := by sorry
