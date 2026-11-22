-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_AFGInner_safe_safe_empty
-- name    : Csg.skirmish_safe_le_AFGInner_safe_safe_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:21:20.9093+00:00
-- url     : https://prove2.me/theorems/f460b005-2181-448b-99a3-98dd4e27ae4e
-- title:
--   Csg: skirmish safe le AFGInner safe safe empty
-- statement:
--   **The payoff, the `x := ∅` analogue.** The exact same post-fixed-point argument, with the
--       escape target threaded through `AFpre1`/`Apre1` set to `∅` instead of `skirmishSafe` -- feeds
--       the `⊥`-level base case `AFGY safe safe ∅` the middle `μX` level's two-step bound needs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L851-L858
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L851-L858

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_AFGInner_safe_safe_empty :
    skirmishSafe ≤
      skirmishCSG.AFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos) skirmishSafe := by sorry
