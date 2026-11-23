-- Prove2me | Theorems.Thm_Csg_skirmish_B_univ_home_hide_eq_univ
-- name    : Csg.skirmish_B_univ_home_hide_eq_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:18:15.946561+00:00
-- url     : https://prove2.me/theorems/21d419fb-2424-43f1-a78c-f1548c98e97f
-- title:
--   Csg: skirmish B univ home hide eq univ
-- statement:
--   **The payoff.** Once `LW` is `Set.univ` (both row actions available with no columns excused),
--       escaping into `{home}` from `hide` succeeds against *every* sniper response: `wait` via `run`
--       (`(run,wait) → home`), `throw` via `hide` (`(hide,throw) → home`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L558-L571
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L558-L571

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_B_univ_home_hide_eq_univ :
    skirmishCSG.B (Set.univ : Set SoldierMove) ({SkirmishPos.home} : Set SkirmishPos)
      SkirmishPos.hide = (Set.univ : Set SniperMove) := by sorry
