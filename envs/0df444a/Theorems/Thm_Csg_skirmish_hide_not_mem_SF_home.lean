-- Prove2me | Theorems.Thm_Csg_skirmish_hide_not_mem_SF_home
-- name    : Csg.skirmish_hide_not_mem_SF_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:11:23.5038+00:00
-- url     : https://prove2.me/theorems/89f5d736-34a6-4be0-9735-89456f382f94
-- title:
--   Csg: skirmish hide not mem SF home
-- statement:
--   **The headline false result.** `<<p1>> sure [ F s=2 ]`: from `hide`, the soldier canNOT force
--       reaching `home` with certainty -- `hide` never even gets *added* to the sure-reachability
--       fixed point, since nothing outside `{home}` can force its way in against an adversarial
--       sniper, in even one more step.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L339-L343
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L339-L343

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_not_mem_SF_home :
    SkirmishPos.hide ∉ skirmishCSG.SF ({SkirmishPos.home} : Set SkirmishPos) := by sorry
