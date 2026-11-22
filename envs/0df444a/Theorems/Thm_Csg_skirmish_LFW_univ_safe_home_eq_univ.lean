-- Prove2me | Theorems.Thm_Csg_skirmish_LFW_univ_safe_home_eq_univ
-- name    : Csg.skirmish_LFW_univ_safe_home_eq_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:23:28.118258+00:00
-- url     : https://prove2.me/theorems/357af9c8-ff8e-472e-a4a1-05ee9d3861c3
-- title:
--   Csg: skirmish LFW univ safe home eq univ
-- statement:
--   **The payoff, the dual case at `home`.** The same argument at `home`: both factors already
--       reduce to `Set.univ` after just *one* step from `⊥` (`skirmish_A_safe_home_eq_univ`,
--       `skirmish_B_univ_safe_home_eq_univ` feeding `CSG.A_univ_v2`), so the second Kleene step (`hbot`
--       substituted into itself) simply reconfirms `Set.univ`, and `OrderHom.map_map_bot_le_lfp` still
--       applies unchanged.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1062-L1098
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1062-L1098

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_LFW_univ_safe_home_eq_univ :
    skirmishCSG.LFW (Set.univ : Set SoldierMove) skirmishSafe skirmishSafe skirmishSafe
        SkirmishPos.home
      = (Set.univ : Set SoldierMove) := by sorry
