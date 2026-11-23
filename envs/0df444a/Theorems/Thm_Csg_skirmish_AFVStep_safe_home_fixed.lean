-- Prove2me | Theorems.Thm_Csg_skirmish_AFVStep_safe_home_fixed
-- name    : Csg.skirmish_AFVStep_safe_home_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:18:20.08778+00:00
-- url     : https://prove2.me/theorems/dd880f43-3cd4-47d3-b04e-acabe141b7f3
-- title:
--   Csg: skirmish AFVStep safe home fixed
-- statement:
--   **The payoff, the dual case at `home`.** `Set.univ` is an *exact* fixed point of `AFVStep safe
--       safe safe` at `home`: both factors collapse to `Set.univ` on their own
--       (`skirmish_A_safe_home_eq_univ`; `skirmish_B_univ_safe_home_eq_univ` feeding `CSG.A_univ_v2`
--       again), so the intersection is `Set.univ` too.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L719-L729
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L719-L729

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AFVStep_safe_home_fixed :
    skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.home
        (Set.univ : Set SoldierMove)
      = (Set.univ : Set SoldierMove) := by sorry
