-- Prove2me | Theorems.Thm_Csg_skirmish_safe_subset_AFpre1_empty_safe_safe
-- name    : Csg.skirmish_safe_subset_AFpre1_empty_safe_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:20:32.301674+00:00
-- url     : https://prove2.me/theorems/84b0bfd7-101b-40ed-9367-88d5b7484a3b
-- title:
--   Csg: skirmish safe subset AFpre1 empty safe safe
-- statement:
--   The Csg construction uses the skirmish safe subset AFpre1 empty safe safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L821-L827
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SkirmishProperties.lean#L821-L827

import Definitions.Def_Csg_Skirmish
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Csg_QualitativeAlmostSure
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Csg_SkirmishProperties
set_option autoImplicit true
open Csg

theorem Csg.skirmish_safe_subset_AFpre1_empty_safe_safe :
    skirmishSafe ⊆ skirmishCSG.AFpre1 (∅ : Set SkirmishPos) skirmishSafe skirmishSafe := by sorry
