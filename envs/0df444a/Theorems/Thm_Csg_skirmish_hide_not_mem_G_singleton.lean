-- Prove2me | Theorems.Thm_Csg_skirmish_hide_not_mem_G_singleton
-- name    : Csg.skirmish_hide_not_mem_G_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:11:02.179455+00:00
-- url     : https://prove2.me/theorems/36d61134-2ce6-4d84-99a1-0cb2e050c9b1
-- title:
--   Csg: skirmish hide not mem G singleton
-- statement:
--   **The headline false result.** `<<p1>> sure [ G s=0 ]`: from `hide`, the soldier canNOT force
--       staying at `hide` forever -- every attempt to hold position is defeated by *some* sniper
--       response (`(hide,throw)` or `(run,wait)`, both landing at `home`), so no single move survives
--       every opponent reply.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L244-L271
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L244-L271

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_not_mem_G_singleton :
    SkirmishPos.hide ∉ skirmishCSG.G ({SkirmishPos.hide} : Set SkirmishPos) := by sorry
