-- Prove2me | Theorems.Thm_Csg_skirmish_hide_not_mem_AF_home
-- name    : Csg.skirmish_hide_not_mem_AF_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:12:09.955288+00:00
-- url     : https://prove2.me/theorems/8010878b-5b44-48b6-8407-81597bc389fa
-- title:
--   Csg: skirmish hide not mem AF home
-- statement:
--   **The headline false result.** `<<p1>> almost [ F s=2 ]`: from `hide`, the soldier canNOT force
--       reaching `home` almost surely (probability 1) -- the first half of the sure/almost-vs-limit
--       divergence LICS 2000 is about.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L456-L459
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L456-L459

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_not_mem_AF_home :
    SkirmishPos.hide ∉ skirmishCSG.AF ({SkirmishPos.home} : Set SkirmishPos) := by sorry
