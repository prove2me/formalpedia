-- Prove2me | Theorems.Thm_Comp_ModelData_mem_bOf
-- name    : Comp.ModelData.mem_bOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:41:09.295793+00:00
-- url     : https://prove2.me/theorems/2fc13aac-85be-4136-aee5-ce7252261535
-- title:
--   Model Data: mem b Of
-- statement:
--   The Model Data construction uses the mem b Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L495-L498
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L495-L498

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_bOf (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    a2 ∈ d.bOf hs v1 x s ↔ ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty := by sorry
