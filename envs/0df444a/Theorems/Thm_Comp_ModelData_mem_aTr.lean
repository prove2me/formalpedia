-- Prove2me | Theorems.Thm_Comp_ModelData_mem_aTr
-- name    : Comp.ModelData.mem_aTr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:39:15.065454+00:00
-- url     : https://prove2.me/theorems/81450322-2003-46f3-9da7-d6c02dddd7b5
-- title:
--   Model Data: mem a Tr
-- statement:
--   The Model Data construction uses the mem a Tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L266-L270
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L266-L270

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_aTr (hs : d.Shape) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    a1 ∈ d.aTr hs v2 y s ↔
      a1 ∈ d.enabled1 hs s ∧ ∀ a2 ∈ d.enabled2 hs s, a2 ∈ v2 ∨ d.supportOf hs s a1 a2 ⊆ y := by sorry
