-- Prove2me | Theorems.Thm_Comp_ModelData_mem_pre1Of
-- name    : Comp.ModelData.mem_pre1Of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:38:49.393234+00:00
-- url     : https://prove2.me/theorems/9e8ead71-99b8-488c-93f3-0991fd0a847f
-- title:
--   Model Data: mem pre1 Of
-- statement:
--   The Model Data construction uses the mem pre1 Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L92-L94
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L92-L94

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_pre1Of (hs : d.Shape) (x : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.pre1Of hs x ↔ ∃ a1, ∀ a2, d.supportOf hs s a1 a2 ⊆ x := by sorry
