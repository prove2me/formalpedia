-- Prove2me | Theorems.Thm_Comp_ModelData_toCsgQ_K
-- name    : Comp.ModelData.toCsgQ_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:38:37.015291+00:00
-- url     : https://prove2.me/theorems/7df40d77-24c3-4b94-8550-a94271fbc515
-- title:
--   Model Data: to Csg Q K
-- statement:
--   The kernel entry, unfolded.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L715-L717
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L715-L717

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.toCsgQ_K (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) (s' : Fin d.nStates) :
    d.toCsgQ.K s a1 a2 s' = denseOf d.nStates (d.transAt s a1 a2).dist s' := by sorry

attribute [defeq] Comp.ModelData.toCsgQ_K
