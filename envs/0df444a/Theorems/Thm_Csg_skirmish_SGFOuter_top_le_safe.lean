-- Prove2me | Theorems.Thm_Csg_skirmish_SGFOuter_top_le_safe
-- name    : Csg.skirmish_SGFOuter_top_le_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:24:46.146833+00:00
-- url     : https://prove2.me/theorems/9c3b01e4-d712-4f4e-b3ac-6f63bd821177
-- title:
--   Csg: skirmish SGFOuter top le safe
-- statement:
--   The Csg construction uses the skirmish SGFOuter top le safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1226-L1229
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1226-L1229

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_SGFOuter_top_le_safe :
    skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) ⊤ ≤ skirmishSafe := by sorry
