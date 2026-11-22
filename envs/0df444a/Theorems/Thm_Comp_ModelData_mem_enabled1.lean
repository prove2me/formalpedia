-- Prove2me | Theorems.Thm_Comp_ModelData_mem_enabled1
-- name    : Comp.ModelData.mem_enabled1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:37:54.780019+00:00
-- url     : https://prove2.me/theorems/6a61d40d-297e-4a29-b493-1d888b14551a
-- title:
--   Model Data: mem enabled1
-- statement:
--   The Model Data construction uses the mem enabled1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L588-L590
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L588-L590

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.mem_enabled1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a1 : Fin d.nAct1) : a1 ∈ d.enabled1 hs s ↔ (a1 : ℕ) ∈ d.keys1 s := by sorry
