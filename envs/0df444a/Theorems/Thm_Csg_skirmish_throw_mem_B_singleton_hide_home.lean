-- Prove2me | Theorems.Thm_Csg_skirmish_throw_mem_B_singleton_hide_home
-- name    : Csg.skirmish_throw_mem_B_singleton_hide_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:18:00.061121+00:00
-- url     : https://prove2.me/theorems/c93958eb-86e2-48ed-a07d-45c1a0b288b8
-- title:
--   Csg: skirmish throw mem B singleton hide home
-- statement:
--   **The payoff.** `throw` escapes into `{home}` from `hide`, using the row action `hide` alone:
--       `(hide,throw) → home`. Feeds the first real step of the inner `LW` computation.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L481-L486
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L481-L486

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_throw_mem_B_singleton_hide_home :
    SniperMove.throw ∈ skirmishCSG.B ({SoldierMove.hide} : Set SoldierMove)
      ({SkirmishPos.home} : Set SkirmishPos) SkirmishPos.hide := by sorry
