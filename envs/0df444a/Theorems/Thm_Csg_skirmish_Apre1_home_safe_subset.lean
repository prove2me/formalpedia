-- Prove2me | Theorems.Thm_Csg_skirmish_Apre1_home_safe_subset
-- name    : Csg.skirmish_Apre1_home_safe_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:05:12.792022+00:00
-- url     : https://prove2.me/theorems/85bcf932-f816-47c0-8ab5-748b9723a9d5
-- title:
--   Csg: skirmish Apre1 home safe subset
-- statement:
--   The Csg construction uses the skirmish Apre1 home safe subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L420-L427
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L420-L427

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_Apre1_home_safe_subset :
    skirmishCSG.Apre1 ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ⊆ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
