-- Prove2me | Theorems.Thm_FongoSync_merged_dup
-- name    : FongoSync.merged_dup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:04.677398+00:00
-- url     : https://prove2.me/theorems/a497eed3-7e4c-4155-b311-bf9a647c7f49
-- title:
--   Fongo Sync: merged dup
-- statement:
--   The Fongo Sync construction uses the merged dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L164-L167
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L164-L167

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merged_dup (σ : String → String → Strategy) (cs : List (Change V))
    (h : ClockDetermines cs) : merged σ (cs ++ cs) = merged σ cs := by sorry
