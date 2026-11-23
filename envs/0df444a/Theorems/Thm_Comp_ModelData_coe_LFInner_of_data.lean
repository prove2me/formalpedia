-- Prove2me | Theorems.Thm_Comp_ModelData_coe_LFInner_of_data
-- name    : Comp.ModelData.coe_LFInner_of_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:25:01.741295+00:00
-- url     : https://prove2.me/theorems/d41114ea-a5aa-4307-9147-ef5c9c7a81d9
-- title:
--   Model Data: coe LFInner of data
-- statement:
--   The Model Data construction uses the coe LFInner of data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L712-L721
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L712-L721

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_LFInner_of_data [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y x : Finset (Fin d.nStates))
    (hlw : ∀ s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅) = (d.lStepOf hs x y s)^[k] ∅) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y ↑x
      = (↑(d.midOf hs k b y x) : Set (Fin d.nStates)) := by sorry
