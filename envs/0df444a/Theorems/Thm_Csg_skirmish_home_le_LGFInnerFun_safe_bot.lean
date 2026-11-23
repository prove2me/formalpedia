-- Prove2me | Theorems.Thm_Csg_skirmish_home_le_LGFInnerFun_safe_bot
-- name    : Csg.skirmish_home_le_LGFInnerFun_safe_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:26:30.156372+00:00
-- url     : https://prove2.me/theorems/aed74581-3b62-4203-b43b-c335a41028f5
-- title:
--   Csg: skirmish home le LGFInner Fun safe bot
-- statement:
--   **The payoff.** `skirmishSafe` is a post-fixed point of `LGFInner {home} skirmishSafe`, one step
--       up from `⊥`, at `home`: `home`'s own second disjunct (`Pre1 skirmishSafe ∩ {home}`) already
--       holds via `skirmishSafe_pre1` (Section 1a). The base case the two-step-up-from-`⊥` bound below
--       starts from.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1341-L1351
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1341-L1351

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_home_le_LGFInnerFun_safe_bot :
    ({SkirmishPos.home} : Set SkirmishPos) ⊆
      skirmishCSG.LGFInner ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
        (⊥ : Set SkirmishPos) := by sorry
