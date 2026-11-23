-- Prove2me | Theorems.Thm_Csg_skirmishReachGoal_eq_SF
-- name    : Csg.skirmishReachGoal_eq_SF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:17:06.361843+00:00
-- url     : https://prove2.me/theorems/0278ed0b-5d95-4b3a-aa9d-ea48d55c87ac
-- title:
--   Csg: skirmish Reach Goal eq SF
-- statement:
--   **The payoff.** `SF {home}` is not merely *at most* `{home}` -- it is *exactly* `{home}`: `⊇`
--       from the general `CSG.subset_SF`; `⊆` from `OrderHom.lfp_le_fixed` applied to
--       `skirmishReachGoal_pre1_empty` (`{home}` is an exact fixed point of `SFOrderHom {home}`, since
--       `Pre1 {home} ∪ {home} = ∅ ∪ {home} = {home}`). The dual of `skirmishSafe_eq_G`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L324-L333
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L324-L333

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmishReachGoal_eq_SF :
    skirmishCSG.SF ({SkirmishPos.home} : Set SkirmishPos) = {SkirmishPos.home} := by sorry
