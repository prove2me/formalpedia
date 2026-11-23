-- Prove2me | Theorems.Thm_Comp_HideOrRun_lpre1F_eq_lpre1C
-- name    : Comp.HideOrRun.lpre1F_eq_lpre1C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:50:21.278804+00:00
-- url     : https://prove2.me/theorems/c60e73b5-7ff3-4fda-9d1f-2c5abe7e94d9
-- title:
--   Hide Or Run: lpre1 F eq lpre1 C
-- statement:
--   The Hide Or Run construction uses the lpre1 F eq lpre1 C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L193-L196
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L193-L196

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun

theorem Comp.HideOrRun.lpre1F_eq_lpre1C (w : HR → Finset Bool) (x : Finset HR) :
    game.lpre1F w x = lpre1C w x := by sorry
