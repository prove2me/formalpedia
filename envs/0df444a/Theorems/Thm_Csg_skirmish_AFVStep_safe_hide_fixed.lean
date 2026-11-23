-- Prove2me | Theorems.Thm_Csg_skirmish_AFVStep_safe_hide_fixed
-- name    : Csg.skirmish_AFVStep_safe_hide_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:18:17.785823+00:00
-- url     : https://prove2.me/theorems/798a184f-5f86-4118-8de0-c7751ff6735f
-- title:
--   Csg: skirmish AFVStep safe hide fixed
-- statement:
--   **The payoff.** `{hide}` is an *exact* fixed point of `AFVStep safe safe safe` at `hide`: the
--       constant first factor is `A ∅ safe hide = {hide}` (`skirmish_A_safe_hide_eq_singleton_hide`);
--       the second factor collapses to `A Set.univ safe hide = Set.univ`
--       (`skirmish_B_singleton_hide_safe_hide_eq_univ` feeding the general `CSG.A_univ_v2`), so the
--       intersection is just the first factor again, on the nose.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L703-L713
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L703-L713

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AFVStep_safe_hide_fixed :
    skirmishCSG.AFVStep skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide
        ({SoldierMove.hide} : Set SoldierMove)
      = ({SoldierMove.hide} : Set SoldierMove) := by sorry
