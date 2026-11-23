-- Prove2me | Theorems.Thm_Comp_ModelData_padFin1_eq_self
-- name    : Comp.ModelData.padFin1_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:52:00.916112+00:00
-- url     : https://prove2.me/theorems/0d93573c-e285-4819-a9ab-654ead3d312b
-- title:
--   Model Data: pad Fin1 eq self
-- statement:
--   `padFin1` is the identity on enabled actions.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L634-L637
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L634-L637

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.padFin1_eq_self (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    {a1 : Fin d.nAct1} (h : a1 ∈ d.enabled1 hs s) : d.padFin1 hs s a1 = a1 := by sorry
