-- Prove2me | Theorems.Thm_FongoSync_Full_view_perm
-- name    : FongoSync.Full.view_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:29.038833+00:00
-- url     : https://prove2.me/theorems/9cf61478-1b2d-42ef-82f9-482a1511cf2c
-- title:
--   Full: view perm
-- statement:
--   The Full construction uses the view perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L421-L423
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L421-L423

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_view_perm

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_perm (sc : Schema) {cs₁ cs₂ : List (Change Value)} (p : cs₁.Perm cs₂)
    (unique : ClockDetermines cs₁) : view sc cs₁ = view sc cs₂ := by sorry
