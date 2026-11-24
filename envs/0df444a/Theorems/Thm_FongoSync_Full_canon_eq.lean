-- Prove2me | Theorems.Thm_FongoSync_Full_canon_eq
-- name    : FongoSync.Full.canon_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:21.386036+00:00
-- url     : https://prove2.me/theorems/4de0e4a5-2935-4d01-87b1-d816f0d611b7
-- title:
--   Full: canon eq
-- statement:
--   The Full construction uses the canon eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L400-L403
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L400-L403

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.canon_eq (unique : ClockDetermines cs₁) : canon sc cs₁ = canon sc cs₂ := by sorry
