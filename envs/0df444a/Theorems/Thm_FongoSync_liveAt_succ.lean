-- Prove2me | Theorems.Thm_FongoSync_liveAt_succ
-- name    : FongoSync.liveAt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:29.682459+00:00
-- url     : https://prove2.me/theorems/0c7572c8-2ca1-4552-a7e9-590f0e2e6636
-- title:
--   Fongo Sync: live At succ
-- statement:
--   The Fongo Sync construction uses the live At succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L43-L44
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L43-L44

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveAt_succ (k : Nat) (g : Gid) :
    liveAt sc inp (k + 1) g ↔ liveAt sc inp k g ∨ rule sc inp (liveAt sc inp k) g := by sorry
