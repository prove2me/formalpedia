-- Prove2me | Theorems.Thm_Csg_skirmish_AGF_home_le_home
-- name    : Csg.skirmish_AGF_home_le_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:26:17.913076+00:00
-- url     : https://prove2.me/theorems/9d1ca048-8126-44c3-98c0-a605cc882a58
-- title:
--   Csg: skirmish AGF home le home
-- statement:
--   **The payoff.** `AGF {home} ≤ {home}`, exactly Section 7b's `skirmish_SGF_home_le_home` with
--       `AGF` substituted for `SGF`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1316-L1325
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1316-L1325

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AGF_home_le_home :
    skirmishCSG.AGF ({SkirmishPos.home} : Set SkirmishPos)
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
