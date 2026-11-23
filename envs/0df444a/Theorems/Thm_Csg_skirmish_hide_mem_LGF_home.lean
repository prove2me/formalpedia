-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_LGF_home
-- name    : Csg.skirmish_hide_mem_LGF_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:22:12.241005+00:00
-- url     : https://prove2.me/theorems/f89a02bb-daf1-43a3-9a5e-7427724e8eed
-- title:
--   Csg: skirmish hide mem LGF home
-- statement:
--   **The headline true result.** `<<p1>> limit [ G F s=2 ]`: from `hide`, the soldier CAN force
--       visiting `home` infinitely often in the limit -- the second headline sure/almost-vs-limit
--       divergence, alongside Section 3/4's reachability one. `OrderHom.le_gfp` applied to
--       `skirmish_safe_le_LGFOuter_safe`, then `hide ∈ skirmishSafe` trivially (`by decide`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1392-L1395
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1392-L1395

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_LGF_home :
    SkirmishPos.hide ∈ skirmishCSG.LGF ({SkirmishPos.home} : Set SkirmishPos) := by sorry
