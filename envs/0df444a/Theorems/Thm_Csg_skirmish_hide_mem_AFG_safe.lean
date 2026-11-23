-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFG_safe
-- name    : Csg.skirmish_hide_mem_AFG_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:13:32.050692+00:00
-- url     : https://prove2.me/theorems/711be9bb-10c9-4a0b-abc8-557dd067e356
-- title:
--   Csg: skirmish hide mem AFG safe
-- statement:
--   **The headline true result.** `<<p1>> almost [ F G !(s=1) ]`: from `hide`, the soldier CAN
--       force eventually always avoiding `wet`, almost surely -- `OrderHom.le_gfp` applied to the outer
--       (`νZ`) post-fixed-point check, `skirmishSafe ≤ AFGX safe safe`, then `hide ∈ skirmishSafe`
--       trivially (`by decide`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L901-L903
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L901-L903

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFG_safe :
    SkirmishPos.hide ∈ skirmishCSG.AFG skirmishSafe := by sorry
