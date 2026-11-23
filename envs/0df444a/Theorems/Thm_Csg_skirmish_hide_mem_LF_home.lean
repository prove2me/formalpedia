-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_LF_home
-- name    : Csg.skirmish_hide_mem_LF_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T01:12:50.384512+00:00
-- url     : https://prove2.me/theorems/cf9f7fe6-fb85-4038-92db-061ed95dac4a
-- title:
--   Csg: skirmish hide mem LF home
-- statement:
--   **The headline true result.** `<<p1>> limit [ F s=2 ]`: from `hide`, the soldier CAN force
--       reaching `home` in the limit -- the other half of the sure/almost-vs-limit divergence LICS
--       2000 is about.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L617-L620
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L617-L620

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_LF_home :
    SkirmishPos.hide ∈ skirmishCSG.LF ({SkirmishPos.home} : Set SkirmishPos) := by sorry
