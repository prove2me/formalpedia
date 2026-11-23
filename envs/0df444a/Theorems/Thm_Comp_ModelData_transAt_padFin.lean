-- Prove2me | Theorems.Thm_Comp_ModelData_transAt_padFin
-- name    : Comp.ModelData.transAt_padFin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:52:24.873241+00:00
-- url     : https://prove2.me/theorems/5c7af286-272c-4d83-85aa-9dae028ecc62
-- title:
--   Model Data: trans At pad Fin
-- statement:
--   Padding invariance at the `Fin` level, which is the form the transfer lemmas use.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L646-L649
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L646-L649

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.transAt_padFin (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.transAt s (d.padFin1 hs s a1) (d.padFin2 hs s a2) = d.transAt s a1 a2 := by sorry
