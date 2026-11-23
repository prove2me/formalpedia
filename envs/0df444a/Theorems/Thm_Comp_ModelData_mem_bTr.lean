-- Prove2me | Theorems.Thm_Comp_ModelData_mem_bTr
-- name    : Comp.ModelData.mem_bTr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:39:22.570907+00:00
-- url     : https://prove2.me/theorems/9c6f3858-ffb9-47c9-a43b-a8bfac745bec
-- title:
--   Model Data: mem b Tr
-- statement:
--   The Model Data construction uses the mem b Tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L273-L277
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L273-L277

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_bTr (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    a2 ∈ d.bTr hs v1 x s ↔
      a2 ∈ d.enabled2 hs s ∧ ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty := by sorry
