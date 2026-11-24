-- Prove2me | Theorems.Thm_FongoSync_step_twice
-- name    : FongoSync.step_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:58.698623+00:00
-- url     : https://prove2.me/theorems/76017d67-b80c-48fd-a23f-4d92bd13fbf0
-- title:
--   Fongo Sync: step twice
-- statement:
--   The Fongo Sync construction uses the step twice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L291-L295
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L291-L295

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.step_twice (sc : Schema) (st : State Value) (a : Change Value) :
    step sc (step sc st a) a = step sc st a := by sorry
