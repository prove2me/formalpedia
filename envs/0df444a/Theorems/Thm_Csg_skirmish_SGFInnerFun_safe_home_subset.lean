-- Prove2me | Theorems.Thm_Csg_skirmish_SGFInnerFun_safe_home_subset
-- name    : Csg.skirmish_SGFInnerFun_safe_home_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:25:15.262774+00:00
-- url     : https://prove2.me/theorems/3b4bfd1c-128f-41fe-8ca1-90cc0af55a91
-- title:
--   Csg: skirmish SGFInner Fun safe home subset
-- statement:
--   **The payoff.** The second step down, from `skirmishSafe` to `{home}`: `wet` is excluded again;
--       `hide` fails outright, since `Pre1 {home} = ∅` (`skirmishReachGoal_pre1_empty`, Section 2a)
--       leaves its first disjunct empty and it isn't `home` itself for the second; `home` survives via
--       the second disjunct, `home ∈ {home}`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1235-L1243
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1235-L1243

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_SGFInnerFun_safe_home_subset :
    skirmishCSG.SGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos)
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
