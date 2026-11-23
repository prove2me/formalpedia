-- Prove2me | Theorems.Thm_Comp_HideOrRun_afInner_at_univ
-- name    : Comp.HideOrRun.afInner_at_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:01:43.788913+00:00
-- url     : https://prove2.me/theorems/670dc90e-62f3-4b1d-8858-edd9dba90a60
-- title:
--   Hide Or Run: af Inner at univ
-- statement:
--   The first outer step, which agrees with the limit-sure one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L317-L321
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L317-L321

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

theorem Comp.HideOrRun.afInner_at_univ :
    ((game.toCSG game_wf).AFInner ↑target ↑(Finset.univ : Finset HR)).lfp =
      (↑winning : Set HR) := by sorry
