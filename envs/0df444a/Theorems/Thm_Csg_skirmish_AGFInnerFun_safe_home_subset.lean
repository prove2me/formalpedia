-- Prove2me | Theorems.Thm_Csg_skirmish_AGFInnerFun_safe_home_subset
-- name    : Csg.skirmish_AGFInnerFun_safe_home_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:26:02.594342+00:00
-- url     : https://prove2.me/theorems/410d31ae-2b44-4bfb-be9b-0c128d8eb65e
-- title:
--   Csg: skirmish AGFInner Fun safe home subset
-- statement:
--   **The payoff.** The second step down, from `skirmishSafe` to `{home}`: `wet` is excluded again;
--       `hide` fails outright, since `Apre1 {home} skirmishSafe ⊆ {home}`
--       (`skirmish_Apre1_home_safe_subset`, Section 3b) rules out its first disjunct while `hide` isn't
--       `home` for the second; `home` survives via the second disjunct.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1299-L1306
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1299-L1306

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AGFInnerFun_safe_home_subset :
    skirmishCSG.AGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos)
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
