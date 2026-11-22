-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFV_empty_safe_safe_home
-- name    : Csg.skirmish_hide_mem_AFV_empty_safe_safe_home
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:19:48.198774+00:00
-- url     : https://prove2.me/theorems/9ebcb9a7-8a95-4420-9294-25a8f15764c3
-- title:
--   Csg: skirmish hide mem AFV empty safe safe home
-- statement:
--   The Csg construction uses the skirmish hide mem AFV empty safe safe home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L807-L811
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L807-L811

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFV_empty_safe_safe_home :
    SoldierMove.hide ∈
      skirmishCSG.AFV (∅ : Set SkirmishPos) skirmishSafe skirmishSafe SkirmishPos.home := by sorry
