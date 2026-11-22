-- Prove2me | Theorems.Thm_Csg_skirmish_hide_not_mem_Apre1_home_safe
-- name    : Csg.skirmish_hide_not_mem_Apre1_home_safe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:17:36.257457+00:00
-- url     : https://prove2.me/theorems/71e85d93-84b0-4bc1-aa5d-ffe842c9e5e9
-- title:
--   Csg: skirmish hide not mem Apre1 home safe
-- statement:
--   **The payoff.** The second step down, from `skirmishSafe` to `{home}`: `wet` is excluded again
--       by `skirmish_wet_not_mem_Apre1`; `hide` needs real work -- restricting to row actions safe for
--       `skirmishSafe` (`A ∅ skirmishSafe hide`) rules out `run` outright (`(run,throw) → wet ∉
--       skirmishSafe`), leaving only `hide` itself, whose *own* outcome against `wait` is `hide`, not
--       `home` -- so `wait` can never be escaped into `{home}`, and `Apre1`'s `B (...) = univ` test
--       fails. Matches the informal check already recorded against `skirmish.prism`: `hide`'s only
--       "safe" move stalls forever against a sniper who always waits.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L396-L418
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L396-L418

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_not_mem_Apre1_home_safe :
    SkirmishPos.hide ∉ skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe := by sorry
