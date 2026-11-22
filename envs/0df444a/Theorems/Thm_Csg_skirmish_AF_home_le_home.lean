-- Prove2me | Theorems.Thm_Csg_skirmish_AF_home_le_home
-- name    : Csg.skirmish_AF_home_le_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:17:56.124706+00:00
-- url     : https://prove2.me/theorems/7bc087e7-2a20-4e59-be83-c1612554bf03
-- title:
--   Csg: skirmish AF home le home
-- statement:
--   **The payoff.** `AF {home} ≤ {home}`: `OrderHom.gfp_le_map_map_top` turns the two hand-checked
--       steps above (`⊤ ↦ skirmishSafe ↦ {home}`) directly into a bound on the actual greatest fixed
--       point, with no need to compute it exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L442-L451
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L442-L451

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AF_home_le_home :
    skirmishCSG.AF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
