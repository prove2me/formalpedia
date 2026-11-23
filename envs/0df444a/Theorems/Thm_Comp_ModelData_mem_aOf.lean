-- Prove2me | Theorems.Thm_Comp_ModelData_mem_aOf
-- name    : Comp.ModelData.mem_aOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:40:43.603466+00:00
-- url     : https://prove2.me/theorems/796456a7-b7f8-440a-8277-ddc2b3437c26
-- title:
--   Model Data: mem a Of
-- statement:
--   The Model Data construction uses the mem a Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L476-L479
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L476-L479

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_aOf (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    a1 ∈ d.aOf hs v2 y s ↔ ∀ a2, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y := by sorry
