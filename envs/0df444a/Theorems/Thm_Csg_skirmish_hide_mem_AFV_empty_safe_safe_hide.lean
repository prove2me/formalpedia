-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFV_empty_safe_safe_hide
-- name    : Csg.skirmish_hide_mem_AFV_empty_safe_safe_hide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:19:42.645239+00:00
-- url     : https://prove2.me/theorems/01608eb4-9083-4a0f-9c44-fb3c06dc48a9
-- title:
--   Csg: skirmish hide mem AFV empty safe safe hide
-- statement:
--   The Csg construction uses the skirmish hide mem AFV empty safe safe hide property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L801-L805
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L801-L805

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFV_empty_safe_safe_hide :
    SoldierMove.hide ∈
      skirmishCSG.AFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.hide := by sorry
