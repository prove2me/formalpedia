-- Prove2me | Theorems.Thm_Comp_ModelData_padFin1_mem
-- name    : Comp.ModelData.padFin1_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:37:42.471791+00:00
-- url     : https://prove2.me/theorems/a36b168d-df22-46b0-b070-1b15cea9a7e2
-- title:
--   Model Data: pad Fin1 mem
-- statement:
--   The Model Data construction uses the pad Fin1 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L608-L611
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L608-L611

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.padFin1_mem (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) : d.padFin1 hs s a1 ∈ d.enabled1 hs s := by sorry
