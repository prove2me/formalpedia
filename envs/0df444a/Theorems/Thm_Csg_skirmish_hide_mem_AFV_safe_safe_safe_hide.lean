-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFV_safe_safe_safe_hide
-- name    : Csg.skirmish_hide_mem_AFV_safe_safe_safe_hide
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:18:33.752092+00:00
-- url     : https://prove2.me/theorems/161503b3-7916-4e2f-88bd-e0227659cf48
-- title:
--   Csg: skirmish hide mem AFV safe safe safe hide
-- statement:
--   **The payoff.** `hide` is a member of `AFV safe safe safe hide` -- `OrderHom.le_gfp` applied to
--       the exact fixed point `skirmish_AFVStep_safe_hide_fixed` (read backwards, as a post-fixed-point
--       hypothesis), then `hide ∈ {hide}` trivially (`rfl`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L734-L737
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L734-L737

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFV_safe_safe_safe_hide :
    SoldierMove.hide ∈ skirmishCSG.AFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide := by sorry
