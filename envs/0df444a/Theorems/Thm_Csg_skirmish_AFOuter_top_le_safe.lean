-- Prove2me | Theorems.Thm_Csg_skirmish_AFOuter_top_le_safe
-- name    : Csg.skirmish_AFOuter_top_le_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:17:22.950035+00:00
-- url     : https://prove2.me/theorems/d4210181-7cc4-4188-a312-5a21c2b98d2b
-- title:
--   Csg: skirmish AFOuter top le safe
-- statement:
--   The Csg construction uses the skirmish AFOuter top le safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L381-L387
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L381-L387

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AFOuter_top_le_safe :
    skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe := by sorry
