-- Prove2me | Theorems.Thm_Comp_ModelData_apre1F_eq
-- name    : Comp.ModelData.apre1F_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:54:12.632591+00:00
-- url     : https://prove2.me/theorems/ac46530b-0565-4b02-9f66-817df100efdb
-- title:
--   Model Data: apre1 F eq
-- statement:
--   The Model Data construction uses the apre1 F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L537-L541
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L537-L541

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.apre1F_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) :
    d.toCsgQ.apre1F x y = d.apre1Of hs x y := by sorry
