-- Prove2me | Theorems.Thm_Csg_skirmishSafe_eq_G
-- name    : Csg.skirmishSafe_eq_G
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:04:14.838418+00:00
-- url     : https://prove2.me/theorems/49f1104c-755e-466b-b869-ebd99a6e1f94
-- title:
--   Csg: skirmish Safe eq G
-- statement:
--   **The payoff.** `G safe` is not merely *at least* `safe` -- it is *exactly* `safe`: `⊆` from
--       the general `CSG.G_subset`; `⊇` from `OrderHom.le_gfp` applied to `skirmishSafe_pre1` (`safe`
--       is already its own witness that it is a pre-fixed point of `GOrderHom safe`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L225-L230
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L225-L230

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmishSafe_eq_G : skirmishCSG.G skirmishSafe = skirmishSafe := by sorry
