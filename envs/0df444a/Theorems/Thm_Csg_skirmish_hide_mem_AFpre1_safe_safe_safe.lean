-- Prove2me | Theorems.Thm_Csg_skirmish_hide_mem_AFpre1_safe_safe_safe
-- name    : Csg.skirmish_hide_mem_AFpre1_safe_safe_safe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:19:08.001259+00:00
-- url     : https://prove2.me/theorems/7284b293-234d-4e65-b629-153984c28484
-- title:
--   Csg: skirmish hide mem AFpre1 safe safe safe
-- statement:
--   The Csg construction uses the skirmish hide mem AFpre1 safe safe safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L748-L750
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L748-L750

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_hide_mem_AFpre1_safe_safe_safe :
    SkirmishPos.hide ∈ skirmishCSG.AFpre1 skirmishSafe skirmishSafe skirmishSafe := by sorry
