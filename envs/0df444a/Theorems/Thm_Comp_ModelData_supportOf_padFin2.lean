-- Prove2me | Theorems.Thm_Comp_ModelData_supportOf_padFin2
-- name    : Comp.ModelData.supportOf_padFin2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:45:40.292606+00:00
-- url     : https://prove2.me/theorems/5e4550db-8ee5-4cc9-85c3-c20fb9889e4c
-- title:
--   Model Data: support Of pad Fin2
-- statement:
--   Nor a column action's.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L748-L752
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L748-L752

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.supportOf_padFin2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.supportOf hs s a1 (d.padFin2 hs s a2) = d.supportOf hs s a1 a2 := by sorry
