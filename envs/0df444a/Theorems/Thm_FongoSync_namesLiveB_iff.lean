-- Prove2me | Theorems.Thm_FongoSync_namesLiveB_iff
-- name    : FongoSync.namesLiveB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:41.650171+00:00
-- url     : https://prove2.me/theorems/1baa14e8-c125-4245-afff-581af92c8a37
-- title:
--   Fongo Sync: names Live B iff
-- statement:
--   The Fongo Sync construction uses the names Live B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L179-L181
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L179-L181

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.namesLiveB_iff {live : Gid → Bool} {p : Gid → Prop} (h : ∀ m, live m = true ↔ p m)
    (o : Gid) : namesLiveB inp live o = true ↔ namesLive inp p o := by sorry
