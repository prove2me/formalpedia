-- Prove2me | Theorems.Thm_Comp_ModelData_mem_lpre1Of
-- name    : Comp.ModelData.mem_lpre1Of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:46:55.217856+00:00
-- url     : https://prove2.me/theorems/b2d55cfc-945c-40d2-8fb2-c518d6c9d141
-- title:
--   Model Data: mem lpre1 Of
-- statement:
--   The Model Data construction uses the mem lpre1 Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L685-L688
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L685-L688

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_lpre1Of (hs : d.Shape) (w : Fin d.nStates → Finset (Fin d.nAct1))
    (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.lpre1Of hs w x ↔ d.bOf hs (w s) x s = Finset.univ := by sorry
