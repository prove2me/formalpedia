-- Prove2me | Theorems.Thm_Comp_ModelData_coe_lmidOf
-- name    : Comp.ModelData.coe_lmidOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:22:52.185801+00:00
-- url     : https://prove2.me/theorems/90261f9d-66c5-4b4c-841c-eda1bffcbb88
-- title:
--   Model Data: coe lmid Of
-- statement:
--   The middle step is `LFInner`, under `Finset.coe`, unconditionally -- the bridge for the middle
--       loop, and the place where `hlw`'s disappearance is cashed in.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L834-L840
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L834-L840

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_wellFormed

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.coe_lmidOf [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y x : Finset (Fin d.nStates)) :
    (↑(d.lmidOf hs b y x) : Set (Fin d.nStates))
      = (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y ↑x := by sorry
