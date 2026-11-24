-- Prove2me | Theorems.Thm_FongoSync_live_of_unowned
-- name    : FongoSync.live_of_unowned
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:27.785685+00:00
-- url     : https://prove2.me/theorems/f021bdb0-ed52-427c-9e75-abab93e35894
-- title:
--   Fongo Sync: live of unowned
-- statement:
--   A known, undeleted entity with no owner fields set is live.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L224-L228
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L224-L228

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.live_of_unowned (sc : Schema) (inp : Inputs) (g : Gid)
    (hk : g ∈ inp.gids) (hd : ¬ deleted sc inp g)
    (ho : ∀ f ∈ sc.fields, f.kind = .owner → register sc inp g f.name = none) :
    Live sc inp g := by sorry
