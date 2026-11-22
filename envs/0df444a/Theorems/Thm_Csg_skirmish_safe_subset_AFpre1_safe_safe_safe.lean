-- Prove2me | Theorems.Thm_Csg_skirmish_safe_subset_AFpre1_safe_safe_safe
-- name    : Csg.skirmish_safe_subset_AFpre1_safe_safe_safe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:19:22.701831+00:00
-- url     : https://prove2.me/theorems/84bcfa7c-b479-4a70-b566-9fc648f5b952
-- title:
--   Csg: skirmish safe subset AFpre1 safe safe safe
-- statement:
--   **The payoff.** Both non-`wet` states qualify for `AFpre1 safe safe safe`, so `skirmishSafe`
--       itself sits inside it -- `wet` is excluded outright (`by decide`, `wet ∉ skirmishSafe` on the
--       hypothesis side makes the `wet` case vacuous). Feeds Section 5f's innermost `νY` post-fixed
--       check directly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L760-L766
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L760-L766

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_subset_AFpre1_safe_safe_safe :
    skirmishSafe ⊆ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe := by sorry
