-- Prove2me | Theorems.Thm_FongoSync_merged_perm
-- name    : FongoSync.merged_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:02.963819+00:00
-- url     : https://prove2.me/theorems/419b3c95-ffee-431f-9686-4ca405f9a3c9
-- title:
--   Fongo Sync: merged perm
-- statement:
--   The Fongo Sync construction uses the merged perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L160-L162
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L160-L162

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.merged_perm (σ : String → String → Strategy) {cs₁ cs₂ : List (Change V)}
    (p : cs₁.Perm cs₂) (h : ClockDetermines cs₁) : merged σ cs₁ = merged σ cs₂ := by sorry
