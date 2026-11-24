-- Prove2me | Theorems.Thm_FongoSync_step_swap
-- name    : FongoSync.step_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:55.968646+00:00
-- url     : https://prove2.me/theorems/02eceb7c-13ef-49d5-a2a6-eab6a77baf2a
-- title:
--   Fongo Sync: step swap
-- statement:
--   The Fongo Sync construction uses the step swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L281-L289
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L281-L289

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.step_swap (sc : Schema) (st : State Value) (a b : Change Value)
    (h : a.field = ALIAS ∨ b.field = ALIAS ∨ Compatible a b) :
    step sc (step sc st a) b = step sc (step sc st b) a := by sorry
