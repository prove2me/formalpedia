-- Prove2me | Theorems.Thm_FongoSync_Laws_view_from_inputs
-- name    : FongoSync.Laws.view_from_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:46.819776+00:00
-- url     : https://prove2.me/theorems/9540eb26-1504-4bfe-9ff5-cba0409cf4f1
-- title:
--   Laws: view from inputs
-- statement:
--   Replicas whose registers, gids and groups agree show the same view.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L154-L156
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L154-L156

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_view_from_inputs

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.view_from_inputs (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (h : inputs sc cs₁ = inputs sc cs₂) : view sc cs₁ = view sc cs₂ := by sorry
