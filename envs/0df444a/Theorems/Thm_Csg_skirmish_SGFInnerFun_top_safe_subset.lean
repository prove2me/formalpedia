-- Prove2me | Theorems.Thm_Csg_skirmish_SGFInnerFun_top_safe_subset
-- name    : Csg.skirmish_SGFInnerFun_top_safe_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:24:50.63291+00:00
-- url     : https://prove2.me/theorems/ce9d9ce7-f7b2-445a-88d9-7d1cf96e8c44
-- title:
--   Csg: skirmish SGFInner Fun top safe subset
-- statement:
--   **The payoff.** One step down from `⊤`: `SGFOuter {home} ⊤ ≤ skirmishSafe` -- `wet` is excluded
--       by `skirmish_wet_not_mem_Pre1`; `hide`/`home` are trivially inside `skirmishSafe` regardless of
--       which disjunct of `SGFInnerFun` actually holds. The `SGF` mirror of Section 3b's
--       `skirmish_Apre1_safe_top_subset`, with `Pre1` standing in for `Apre1` on the non-`b` branch.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1213-L1224
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1213-L1224

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_SGFInnerFun_top_safe_subset :
    skirmishCSG.SGFInnerFun ({SkirmishPos.home} : Set SkirmishPos) (⊤ : Set SkirmishPos)
        skirmishSafe
      ⊆ skirmishSafe := by sorry
