-- Prove2me | Theorems.Thm_FongoSync_view_perm
-- name    : FongoSync.view_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:12.239262+00:00
-- url     : https://prove2.me/theorems/323b9170-b026-42ec-97de-0e93e22f0d96
-- title:
--   Fongo Sync: view perm
-- statement:
--   The Fongo Sync construction uses the view perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L341-L343
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L341-L343

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.view_perm (sc : Schema) {cs₁ cs₂ : List (Change Value)} (p : cs₁.Perm cs₂)
    (unique : ClockDetermines cs₁) : view sc cs₁ = view sc cs₂ := by sorry
