-- Prove2me | Theorems.Thm_Csg_skirmish_B_univ_safe_home_eq_univ
-- name    : Csg.skirmish_B_univ_safe_home_eq_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:06:14.128885+00:00
-- url     : https://prove2.me/theorems/a7814862-5403-481e-ae4b-fc3ec7a21452
-- title:
--   Csg: skirmish B univ safe home eq univ
-- statement:
--   **The payoff.** Every sniper response escapes into `skirmishSafe` from `home`, for *any*
--       row-action pool containing `hide` (in particular `Set.univ`): `home`'s transition lands at
--       `hide ∈ skirmishSafe` regardless of the sniper's move, so `hide` alone already witnesses the
--       escape for every `a2`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L687-L694
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L687-L694

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_B_univ_safe_home_eq_univ :
    skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.home
      = (Set.univ : Set SniperMove) := by sorry
