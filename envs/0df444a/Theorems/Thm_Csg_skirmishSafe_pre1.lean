-- Prove2me | Theorems.Thm_Csg_skirmishSafe_pre1
-- name    : Csg.skirmishSafe_pre1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:00:01.92626+00:00
-- url     : https://prove2.me/theorems/724a3d3f-ac97-4220-8626-276b3601c1dc
-- title:
--   Csg: skirmish Safe pre1
-- statement:
--   **The payoff.** `skirmishSafe` is a pre-fixed point of `Pre1`: from `hide`, staying put
--       (`.hide`) keeps every sniper response inside `safe`; from `home`, *any* soldier move does,
--       since `skirmishK_support_home` lands back at `hide ∈ safe` unconditionally regardless of the
--       joint move.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L200-L218
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L200-L218

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmishSafe_pre1 : skirmishSafe ⊆ skirmishCSG.Pre1 skirmishSafe := by sorry
