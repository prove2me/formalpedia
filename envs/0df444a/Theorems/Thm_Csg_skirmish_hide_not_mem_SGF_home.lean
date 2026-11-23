-- Prove2me | Theorems.Thm_Csg_skirmish_hide_not_mem_SGF_home
-- name    : Csg.skirmish_hide_not_mem_SGF_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:16:42.352585+00:00
-- url     : https://prove2.me/theorems/efca3263-d18c-45f3-b59d-2eec6cf804a3
-- title:
--   Csg: skirmish hide not mem SGF home
-- statement:
--   **The headline false result.** `<<p1>> sure [ G F s=2 ]`: from `hide`, the soldier canNOT force
--       visiting `home` infinitely often with certainty.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1267-L1270
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1267-L1270

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_not_mem_SGF_home :
    SkirmishPos.hide ∉ skirmishCSG.SGF ({SkirmishPos.home} : Set SkirmishPos) := by sorry
