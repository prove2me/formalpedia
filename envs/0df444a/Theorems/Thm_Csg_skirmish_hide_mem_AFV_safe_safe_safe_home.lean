-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFV_safe_safe_safe_home
-- name    : Csg.skirmish_hide_mem_AFV_safe_safe_safe_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:18:55.600224+00:00
-- url     : https://prove2.me/theorems/09987979-0577-40cc-86c8-6cf8d163f99b
-- title:
--   Csg: skirmish hide mem AFV safe safe safe home
-- statement:
--   **The payoff, the dual case at `home`.** `hide` is a member of `AFV safe safe safe home` too --
--       the fixed point there is `Set.univ`, so *any* `SoldierMove` is a member, `hide` included.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L741-L744
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L741-L744

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFV_safe_safe_safe_home :
    SoldierMove.hide ∈ skirmishCSG.AFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home := by sorry
