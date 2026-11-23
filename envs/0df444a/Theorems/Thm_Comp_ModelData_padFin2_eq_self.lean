-- Prove2me | Theorems.Thm_Comp_ModelData_padFin2_eq_self
-- name    : Comp.ModelData.padFin2_eq_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:51:59.193241+00:00
-- url     : https://prove2.me/theorems/6d5f8eb7-ba3c-4f06-b4c9-fbe99446d398
-- title:
--   Model Data: pad Fin2 eq self
-- statement:
--   The column-side mirror.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L640-L643
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L640-L643

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.padFin2_eq_self (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    {a2 : Fin d.nAct2} (h : a2 ∈ d.enabled2 hs s) : d.padFin2 hs s a2 = a2 := by sorry
