-- Prove2me | Theorems.Thm_Csg_skirmish_SGFOuter_safe_le_home
-- name    : Csg.skirmish_SGFOuter_safe_le_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:25:35.049133+00:00
-- url     : https://prove2.me/theorems/67a65865-b556-4aa8-8c26-a487dd0874bc
-- title:
--   Csg: skirmish SGFOuter safe le home
-- statement:
--   The Csg construction uses the skirmish SGFOuter safe le home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1245-L1249
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1245-L1249

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_SGFOuter_safe_le_home :
    skirmishCSG.SGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
