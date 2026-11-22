-- Prove2me | Theorems.Thm_Csg_skirmish_safe_le_LFGX_safe_safe
-- name    : Csg.skirmish_safe_le_LFGX_safe_safe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:24:16.292637+00:00
-- url     : https://prove2.me/theorems/f71eaf44-f69c-4720-ab4e-0f2769c86b43
-- title:
--   Csg: skirmish safe le LFGX safe safe
-- statement:
--   **The payoff, the middle `μX` level -- the `LFG` mirror of Section 5f's `skirmish_safe_le_
--       AFGX_safe_safe`.** `skirmishSafe ≤ LFGX safe safe`: chase `LFGY`'s own monotonicity in `x`
--       (`CSG.LFGY_mono_x`, already general-purpose infrastructure in `Csg.QualitativeLimitSure`) from
--       the `⊥`-level bound up to `skirmishSafe` itself, then hand the resulting two-step-from-`⊥`
--       lower bound to `OrderHom.map_map_bot_le_lfp` -- line-for-line the same shape as `AFG`'s own
--       version, with `LFG*` substituted for `AFG*` throughout.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1157-L1180
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1157-L1180

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_le_LFGX_safe_safe :
    skirmishSafe ≤ skirmishCSG.LFGX skirmishSafe skirmishSafe := by sorry
