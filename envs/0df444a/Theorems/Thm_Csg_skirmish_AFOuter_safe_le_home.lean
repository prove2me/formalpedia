-- Prove2me | Theorems.Thm_Csg_skirmish_AFOuter_safe_le_home
-- name    : Csg.skirmish_AFOuter_safe_le_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:17:40.851486+00:00
-- url     : https://prove2.me/theorems/b0eae506-3b25-4602-9d59-b8d9969adc59
-- title:
--   Csg: skirmish AFOuter safe le home
-- statement:
--   The Csg construction uses the skirmish AFOuter safe le home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L429-L435
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L429-L435

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_AFOuter_safe_le_home :
    skirmishCSG.AFOuter ({SkirmishPos.home} : Set SkirmishPos) skirmishSafe
      ≤ ({SkirmishPos.home} : Set SkirmishPos) := by sorry
