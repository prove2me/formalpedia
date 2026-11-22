-- Prove2me | Theorems.Thm_Comp_ModelData_mem_lpre1Tr
-- name    : Comp.ModelData.mem_lpre1Tr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:40:12.929887+00:00
-- url     : https://prove2.me/theorems/cbb21681-3aeb-402a-8e36-b740a0a85e36
-- title:
--   Model Data: mem lpre1 Tr
-- statement:
--   The Model Data construction uses the mem lpre1 Tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L446-L449
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L446-L449

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_lpre1Tr (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.lpre1Tr hs w x ↔ d.bTr hs (w s) x s = d.enabled2 hs s := by sorry
