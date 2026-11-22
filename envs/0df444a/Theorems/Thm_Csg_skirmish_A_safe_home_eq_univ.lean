-- Prove2me | Theorems.Thm_Csg_skirmish_A_safe_home_eq_univ
-- name    : Csg.skirmish_A_safe_home_eq_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:55:28.992219+00:00
-- url     : https://prove2.me/theorems/8af85dbf-1406-4afd-9144-a2adb27c7b5c
-- title:
--   Csg: skirmish A safe home eq univ
-- statement:
--   **The payoff, no case split needed at all.** Every row action is safe for `skirmishSafe` at
--       `home`, columns unexcused: `home`'s transition (`skirmishK_support_home`) lands at `hide ∈
--       skirmishSafe` unconditionally, regardless of *either* half of the joint move.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L653-L659
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L653-L659

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_A_safe_home_eq_univ :
    skirmishCSG.A (∅ : Set SniperMove) skirmishSafe SkirmishPos.home = Set.univ := by sorry
