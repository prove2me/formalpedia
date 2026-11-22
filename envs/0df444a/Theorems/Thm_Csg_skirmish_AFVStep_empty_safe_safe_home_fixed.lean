-- Prove2me | Theorems.Thm_Csg_skirmish_AFVStep_empty_safe_safe_home_fixed
-- name    : Csg.skirmish_AFVStep_empty_safe_safe_home_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:19:40.725708+00:00
-- url     : https://prove2.me/theorems/1ee1f668-e330-4d2b-91d5-2c13ec8c3e6c
-- title:
--   Csg: skirmish AFVStep empty safe safe home fixed
-- statement:
--   **The payoff, the dual case at `home`.** The same constant-map collapse, at `home`: both
--       factors reduce to `A ∅ safe home = Set.univ`, so `Set.univ` is the (trivial) exact fixed
--       point.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L790-L799
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L790-L799

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AFVStep_empty_safe_safe_home_fixed :
    skirmishCSG.AFVStep (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home
        (Set.univ : Set SoldierMove)
      = (Set.univ : Set SoldierMove) := by sorry
