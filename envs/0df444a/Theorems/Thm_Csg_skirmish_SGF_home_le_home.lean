-- Prove2me | Theorems.Thm_Csg_skirmish_SGF_home_le_home
-- name    : Csg.skirmish_SGF_home_le_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:25:29.226256+00:00
-- url     : https://prove2.me/theorems/8c0bed83-210e-48ad-8f7f-e2438c8b868c
-- title:
--   Csg: skirmish SGF home le home
-- statement:
--   **The payoff.** `SGF {home} ≤ {home}`: `OrderHom.gfp_le_map_map_top` turns the two hand-checked
--       steps above (`⊤ ↦ skirmishSafe ↦ {home}`) directly into a bound on the actual greatest fixed
--       point, exactly Section 3c's `skirmish_AF_home_le_home` with `SGF` substituted for `AF`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1254-L1263
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1254-L1263

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_SGF_home_le_home :
    skirmishCSG.SGF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
