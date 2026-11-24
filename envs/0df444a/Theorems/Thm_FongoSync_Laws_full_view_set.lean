-- Prove2me | Theorems.Thm_FongoSync_Laws_full_view_set
-- name    : FongoSync.Laws.full_view_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:07:00.867177+00:00
-- url     : https://prove2.me/theorems/d0d4e0a5-e5e0-46dd-9528-fd1f4c4a2441
-- title:
--   Laws: full view set
-- statement:
--   **The view over several collections depends only on the set of changes**, given unique
--   clocks per register.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L191-L194
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L191-L194

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.full_view_set (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    Full.view sc cs₁ = Full.view sc cs₂ := by sorry
