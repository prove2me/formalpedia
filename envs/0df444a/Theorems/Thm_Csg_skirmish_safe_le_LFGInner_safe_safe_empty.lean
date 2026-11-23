-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_LFGInner_safe_safe_empty
-- name    : Csg.skirmish_safe_le_LFGInner_safe_safe_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:22:09.146136+00:00
-- url     : https://prove2.me/theorems/df252aea-5d28-428f-a404-f0af5bc3e6c2
-- title:
--   Csg: skirmish safe le LFGInner safe safe empty
-- statement:
--   **The payoff, the `LFG` mirror of Section 5f's `AFG` version.** `skirmishSafe` is a post-fixed
--       point of `LFGInner safe safe ∅`, at `y = safe`: every `s ∈ safe` takes the `b`-branch, since it
--       is already in both conjuncts (`skirmish_safe_subset_LFpre1_empty_safe_safe`, and `hs` itself).
--       Feeds the `⊥`-level base case the middle `μX` level's two-step bound needs.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L995-L1002
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L995-L1002

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_LFGInner_safe_safe_empty :
    skirmishSafe ≤
      skirmishCSG.LFGInner skirmishSafe skirmishSafe (∅ : Set SkirmishPos) skirmishSafe := by sorry
