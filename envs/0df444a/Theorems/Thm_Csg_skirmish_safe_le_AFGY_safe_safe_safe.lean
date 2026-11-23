-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_AFGY_safe_safe_safe
-- name    : Csg.skirmish_safe_le_AFGY_safe_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:21:11.548201+00:00
-- url     : https://prove2.me/theorems/c68e630d-2b86-4deb-8730-28cc995c680c
-- title:
--   Csg: skirmish safe le AFGY safe safe safe
-- statement:
--   **The payoff.** `skirmishSafe ≤ AFGY safe safe safe` -- `OrderHom.le_gfp` applied directly to
--       the post-fixed-point check above.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L843-L846
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L843-L846

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_AFGY_safe_safe_safe :
    skirmishSafe ≤ skirmishCSG.AFGY skirmishSafe skirmishSafe skirmishSafe := by sorry
