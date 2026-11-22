-- Prove2me | Theorems.Thm_Csg_skirmish_AGFInnerFun_top_safe_subset
-- name    : Csg.skirmish_AGFInnerFun_top_safe_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:25:42.224462+00:00
-- url     : https://prove2.me/theorems/e3355958-3e95-4d85-a5c8-5e1e646eb0b2
-- title:
--   Csg: skirmish AGFInner Fun top safe subset
-- statement:
--   **The payoff.** One step down from `⊤`: `AGFOuter {home} ⊤ ≤ skirmishSafe` -- the `AGF` mirror
--       of `skirmish_SGFInnerFun_top_safe_subset`, with `Apre1` standing in for `Pre1` on the non-`b`
--       branch and `skirmish_wet_not_mem_Apre1` (Section 3a) excluding `wet`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1277-L1288
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1277-L1288

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AGFInnerFun_top_safe_subset :
    skirmishCSG.AGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) (⊤ : Set SkirmishPos)
        skirmishSafe
      ⊆ skirmishSafe := by sorry
