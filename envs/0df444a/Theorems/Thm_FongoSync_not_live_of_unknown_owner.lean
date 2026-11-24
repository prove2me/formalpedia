-- Prove2me | Theorems.Thm_FongoSync_not_live_of_unknown_owner
-- name    : FongoSync.not_live_of_unknown_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:42.611087+00:00
-- url     : https://prove2.me/theorems/2fa8137e-cfe9-409c-b192-e1729afff3b0
-- title:
--   Fongo Sync: not live of unknown owner
-- statement:
--   An entity whose owner field names something unknown is never live.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L242-L255
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L242-L255

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.not_live_of_unknown_owner (sc : Schema) (inp : Inputs) (g o : Gid) (f : Field)
    (hf : f ∈ sc.fields) (hkind : f.kind = .owner) (e : Entry Value)
    (he : register sc inp g f.name = some e) (hv : e.value = .ref o) (ho : o ∉ inp.gids) :
    ¬ Live sc inp g := by sorry
