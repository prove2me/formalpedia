-- Prove2me | Theorems.Thm_Comp_ModelData_lpre1F_eq
-- name    : Comp.ModelData.lpre1F_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:41:43.901867+00:00
-- url     : https://prove2.me/theorems/5b3c57bf-7fbe-4c24-8044-36b0367ba928
-- title:
--   Model Data: lpre1 F eq
-- statement:
--   The Model Data construction uses the lpre1 F eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L690-L694
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L690-L694

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.lpre1F_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (w : Fin d.nStates → Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates)) :
    d.toCsgQ.lpre1F w x = d.lpre1Of hs w x := by sorry
