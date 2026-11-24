-- Prove2me | Theorems.Thm_FongoSync_rule_congr
-- name    : FongoSync.rule_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:32.430336+00:00
-- url     : https://prove2.me/theorems/605757c5-607d-462b-8bde-ed02d79e6fd6
-- title:
--   Fongo Sync: rule congr
-- statement:
--   The rule only looks at live sets on the gids.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L47-L61
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L47-L61

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.rule_congr {p q : Gid → Prop} (h : ∀ m ∈ inp.gids, p m ↔ q m) (g : Gid) :
    rule sc inp p g ↔ rule sc inp q g := by sorry
