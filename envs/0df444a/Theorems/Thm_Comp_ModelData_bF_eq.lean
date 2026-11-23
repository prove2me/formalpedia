-- Prove2me | Theorems.Thm_Comp_ModelData_bF_eq
-- name    : Comp.ModelData.bF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:42:29.670578+00:00
-- url     : https://prove2.me/theorems/2143e41d-37f5-4e3e-898a-d6b3e6601010
-- title:
--   Model Data: b F eq
-- statement:
--   The Model Data construction uses the b F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L500-L505
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L500-L505

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.bF_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.toCsgQ.bF v1 x s = d.bOf hs v1 x s := by sorry
