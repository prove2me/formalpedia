-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_AFGX_safe_safe
-- name    : Csg.skirmish_safe_le_AFGX_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:21:25.314052+00:00
-- url     : https://prove2.me/theorems/6cf11e46-7b0b-493b-8eac-b0a8952a5cd1
-- title:
--   Csg: skirmish safe le AFGX safe safe
-- statement:
--   **The payoff, the middle `μX` level.** `skirmishSafe ≤ AFGX safe safe`: chase `AFGY`'s own
--       monotonicity in `x` (`CSG.AFGY_mono_x`) from the `⊥`-level bound just established up to
--       `skirmishSafe` itself, giving a two-step-from-`⊥` lower bound on `AFGMiddle safe safe`'s image,
--       then hand it to `OrderHom.map_map_bot_le_lfp` -- the exact same technique Section 4c uses for
--       `LFOuter`, nested one level deeper here.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L870-L893
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L870-L893

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_AFGX_safe_safe :
    skirmishSafe ≤ skirmishCSG.AFGX skirmishSafe skirmishSafe := by sorry
