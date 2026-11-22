-- Prove2me | Theorems.Thm_Comp_ModelData_padFin2_mem
-- name    : Comp.ModelData.padFin2_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:38:10.835584+00:00
-- url     : https://prove2.me/theorems/71185b1c-e578-4c1f-b9ed-49501ed5182b
-- title:
--   Model Data: pad Fin2 mem
-- statement:
--   The Model Data construction uses the pad Fin2 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L614-L617
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L614-L617

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.padFin2_mem (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a2 : Fin d.nAct2) : d.padFin2 hs s a2 ∈ d.enabled2 hs s := by sorry
