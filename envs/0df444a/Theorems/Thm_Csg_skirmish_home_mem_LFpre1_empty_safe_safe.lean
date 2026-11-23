-- Prove2me | Theorems.Thm_Csg_skirmish_home_mem_LFpre1_empty_safe_safe
-- name    : Csg.skirmish_home_mem_LFpre1_empty_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:21:39.452305+00:00
-- url     : https://prove2.me/theorems/7e8f4a18-9fc8-403e-b683-b90ab055f637
-- title:
--   Csg: skirmish home mem LFpre1 empty safe safe
-- statement:
--   The Csg construction uses the skirmish home mem LFpre1 empty safe safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L974-L979
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L974-L979

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_home_mem_LFpre1_empty_safe_safe :
    SkirmishPos.home ∈ skirmishCSG.LFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by sorry
