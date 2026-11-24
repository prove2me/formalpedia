-- Prove2me | Theorems.Thm_FongoSync_registers_eq_merged
-- name    : FongoSync.registers_eq_merged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:02.351775+00:00
-- url     : https://prove2.me/theorems/fa19d30e-5247-47e9-8e82-167b5903e807
-- title:
--   Fongo Sync: registers eq merged
-- statement:
--   The Fongo Sync construction uses the registers eq merged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L297-L302
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L297-L302

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.registers_eq_merged (sc : Schema) (cs : List (Change Value)) :
    registers sc cs = merged sc.strategyOf (cs.filter fun c => c.field ≠ ALIAS) := by sorry
