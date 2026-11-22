-- Prove2me | Theorems.Thm_Csg_skirmish_AGFOuter_safe_le_home
-- name    : Csg.skirmish_AGFOuter_safe_le_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:26:17.772848+00:00
-- url     : https://prove2.me/theorems/440b6bed-acd2-4da3-b3db-f351d0a3f1bc
-- title:
--   Csg: skirmish AGFOuter safe le home
-- statement:
--   The Csg construction uses the skirmish AGFOuter safe le home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1308-L1312
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L1308-L1312

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AGFOuter_safe_le_home :
    skirmishCSG.AGFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
