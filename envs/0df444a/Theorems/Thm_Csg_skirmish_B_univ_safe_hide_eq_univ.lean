-- Prove2me | Theorems.Thm_Csg_skirmish_B_univ_safe_hide_eq_univ
-- name    : Csg.skirmish_B_univ_safe_hide_eq_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:21:32.742814+00:00
-- url     : https://prove2.me/theorems/2b39b925-8dde-44fc-8d3c-b61a013a55fc
-- title:
--   Csg: skirmish B univ safe hide eq univ
-- statement:
--   **The payoff.** A one-line monotonicity lift of Section 5b's `skirmish_B_singleton_hide_safe_
--       hide_eq_univ`: widening the row-action pool from `{hide}` to `Set.univ` can only add escapes,
--       and the target is already `Set.univ` on the nose, so equality survives.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L910-L919
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L910-L919

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_B_univ_safe_hide_eq_univ :
    skirmishCSG.B (Set.univ : Set SoldierMove) skirmishSafe SkirmishPos.hide
      = (Set.univ : Set SniperMove) := by sorry
