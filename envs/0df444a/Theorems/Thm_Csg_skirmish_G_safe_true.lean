-- Prove2me | Theorems.Thm_Csg_skirmish_G_safe_true
-- name    : Csg.skirmish_G_safe_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:09:00.948422+00:00
-- url     : https://prove2.me/theorems/f438a272-8445-44b2-a37e-a3da0f31b3a7
-- title:
--   Csg: skirmish G safe true
-- statement:
--   **The headline true result.** `<<p1>> sure [ G !(s=1) ]`: from `hide`, the soldier can force
--       avoiding `wet` forever, with certainty.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L234-L236
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L234-L236

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_G_safe_true : SkirmishPos.hide ∈ skirmishCSG.G skirmishSafe := by sorry
