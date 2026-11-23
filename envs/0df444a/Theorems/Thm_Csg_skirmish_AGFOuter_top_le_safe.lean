-- Prove2me | Theorems.Thm_Csg_skirmish_AGFOuter_top_le_safe
-- name    : Csg.skirmish_AGFOuter_top_le_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:25:45.165021+00:00
-- url     : https://prove2.me/theorems/29c71f19-d490-4ce1-bff6-d59149ae946d
-- title:
--   Csg: skirmish AGFOuter top le safe
-- statement:
--   The Csg construction uses the skirmish AGFOuter top le safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1290-L1293
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1290-L1293

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AGFOuter_top_le_safe :
    skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe := by sorry
