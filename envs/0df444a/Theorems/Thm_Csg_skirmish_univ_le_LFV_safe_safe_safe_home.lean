-- Prove2me | Theorems.Thm_Csg_skirmish_univ_le_LFV_safe_safe_safe_home
-- name    : Csg.skirmish_univ_le_LFV_safe_safe_safe_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:23:42.555168+00:00
-- url     : https://prove2.me/theorems/48c68924-cb04-49b0-9675-20c8edf28aa2
-- title:
--   Csg: skirmish univ le LFV safe safe safe home
-- statement:
--   **The payoff, the dual case at `home`.**
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1113-L1117
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1113-L1117

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_univ_le_LFV_safe_safe_safe_home :
    (Set.univ : Set SoldierMove) ≤
      skirmishCSG.LFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home := by sorry
