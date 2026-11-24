-- Prove2me | Theorems.Thm_FongoSync_Laws_view_set
-- name    : FongoSync.Laws.view_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:55.094378+00:00
-- url     : https://prove2.me/theorems/e5336f1f-7936-4341-a95d-96f041647e8d
-- title:
--   Laws: view set
-- statement:
--   **The view depends only on the set of changes**, given unique clocks per register.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L182-L185
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L182-L185

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.view_set (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    view sc cs₁ = view sc cs₂ := by sorry
