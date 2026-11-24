-- Prove2me | Theorems.Thm_FongoSync_Laws_view_runs
-- name    : FongoSync.Laws.view_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:52.265201+00:00
-- url     : https://prove2.me/theorems/daf53265-58ae-400b-8a6a-a824419ed185
-- title:
--   Laws: view runs
-- statement:
--   The view can be computed: `runView` applies the liveness rule once per gid and gives the
--   same answer.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L178-L179
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L178-L179

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.view_runs (sc : Schema) (cs : List (Change Value)) : runView sc cs = view sc cs := by sorry
