-- Prove2me | Theorems.Thm_Csg_skirmish_LW_home_safe_hide_eq_univ
-- name    : Csg.skirmish_LW_home_safe_hide_eq_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:18:05.054493+00:00
-- url     : https://prove2.me/theorems/2872200f-9547-4cb5-95ce-71b5a24e5fd4
-- title:
--   Csg: skirmish LW home safe hide eq univ
-- statement:
--   **The payoff.** The inner row-action witness set `LW` reaches `Set.univ` at `hide`, against
--       goal `{home}` and safety target `skirmishSafe`, in exactly two steps up from `⊥`:
--       `∅ ↦ {hide} ↦ {hide, run} = univ`. `OrderHom.map_map_bot_le_lfp` turns this two-step hand
--       computation directly into a lower bound on the actual least fixed point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L520-L553
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L520-L553

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_LW_home_safe_hide_eq_univ :
    skirmishCSG.LW ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SoldierMove) := by sorry
