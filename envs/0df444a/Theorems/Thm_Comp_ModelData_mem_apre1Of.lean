-- Prove2me | Theorems.Thm_Comp_ModelData_mem_apre1Of
-- name    : Comp.ModelData.mem_apre1Of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:41:46.924369+00:00
-- url     : https://prove2.me/theorems/0d04b72f-8fa8-4e61-a356-a541a9ba4724
-- title:
--   Model Data: mem apre1 Of
-- statement:
--   The Model Data construction uses the mem apre1 Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L533-L535
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L533-L535

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_apre1Of (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.apre1Of hs x y ↔ d.bOf hs (d.aOf hs ∅ y s) x s = Finset.univ := by sorry
