-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_LFG_safe
-- name    : Csg.skirmish_hide_mem_LFG_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:14:50.84658+00:00
-- url     : https://prove2.me/theorems/41bce91a-6181-4d7e-955c-e3694d568935
-- title:
--   Csg: skirmish hide mem LFG safe
-- statement:
--   **The headline true result.** `<<p1>> limit [ F G !(s=1) ]`: from `hide`, the soldier CAN force
--       eventually always avoiding `wet`, in the limit -- `OrderHom.le_gfp` applied to the outer (`νZ`)
--       post-fixed-point check, `skirmishSafe ≤ LFGX safe safe`, then `hide ∈ skirmishSafe` trivially
--       (`by decide`). The last of this file's `sure`/`almost`/`limit` facts before Büchi (`GF`),
--       deferred to its own section.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1189-L1191
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1189-L1191

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_LFG_safe :
    SkirmishPos.hide ∈ skirmishCSG.LFG skirmishSafe := by sorry
