-- Prove2me | Theorems.Thm_Comp_ModelData_mem_apre1Tr
-- name    : Comp.ModelData.mem_apre1Tr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:39:42.430802+00:00
-- url     : https://prove2.me/theorems/cd959a9d-0271-4f96-9aa2-ead88ab8729f
-- title:
--   Model Data: mem apre1 Tr
-- statement:
--   The Model Data construction uses the mem apre1 Tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L424-L426
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L424-L426

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.mem_apre1Tr (hs : d.Shape) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) :
    s ∈ d.apre1Tr hs x y ↔ d.bTr hs (d.aTr hs ∅ y s) x s = d.enabled2 hs s := by sorry
