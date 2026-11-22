-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_LGFInnerFun_safe_home
-- name    : Csg.skirmish_safe_le_LGFInnerFun_safe_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:26:33.431919+00:00
-- url     : https://prove2.me/theorems/a27ab0bb-d267-48f6-8b46-14cab41ee1d7
-- title:
--   Csg: skirmish safe le LGFInner Fun safe home
-- statement:
--   **The payoff.** `skirmishSafe` maps into `LGFInnerFun {home} skirmishSafe {home}`: `hide` via
--       its first disjunct, `skirmish_hide_mem_Lpre1_home_safe` (Section 4b) doing all the real work
--       exactly as it did for `LF` itself; `home` via the second disjunct, `skirmishSafe_pre1` again.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1356-L1364
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1356-L1364

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_LGFInnerFun_safe_home :
    skirmishSafe ⊆
      skirmishCSG.LGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        ({SkirmishPos.home} : Set SkirmishPos) := by sorry
