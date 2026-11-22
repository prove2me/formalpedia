-- Prove2me | Theorems.Thm_Csg_skirmish_univ_le_LFV_safe_safe_safe_hide
-- name    : Csg.skirmish_univ_le_LFV_safe_safe_safe_hide
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:23:28.42159+00:00
-- url     : https://prove2.me/theorems/74f7591c-ff58-48b6-93a3-a1c20df91a67
-- title:
--   Csg: skirmish univ le LFV safe safe safe hide
-- statement:
--   **The payoff.** `Set.univ` is a post-fixed point of `LFVStep safe safe safe hide` at itself
--       (`LFVStep`'s own value there is exactly `LFW Set.univ safe safe safe hide`,
--       `skirmish_LFW_univ_safe_hide_eq_univ`) -- `OrderHom.le_gfp` turns this into a lower bound on
--       the actual `LFV`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1106-L1110
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1106-L1110

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_univ_le_LFV_safe_safe_safe_hide :
    (Set.univ : Set SoldierMove) ≤
      skirmishCSG.LFV skirmishSafe skirmishSafe skirmishSafe SkirmishPos.hide := by sorry
