-- Prove2me | Theorems.Thm_Csg_skirmish_SFG_safe_true
-- name    : Csg.skirmish_SFG_safe_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:11:18.943802+00:00
-- url     : https://prove2.me/theorems/68885b3a-cb10-43c6-81b2-b5683be2506b
-- title:
--   Csg: skirmish SFG safe true
-- statement:
--   **The regression check.** `<<p1>> sure [ F G !(s=1) ]`: once "always avoid `wet`" is already
--       forceable (`skirmish_G_safe_true`), "eventually always avoid `wet`" is immediate -- reaching a
--       set you already occupy takes no strategy at all (`CSG.subset_SF`). No new fixed-point content
--       beyond `skirmishSafe_eq_G`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L279-L282
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L279-L282

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_SFG_safe_true : SkirmishPos.hide ∈ skirmishCSG.SFG skirmishSafe := by sorry
