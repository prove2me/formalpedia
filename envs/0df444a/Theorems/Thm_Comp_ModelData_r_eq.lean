-- Prove2me | Theorems.Thm_Comp_ModelData_r_eq
-- name    : Comp.ModelData.r_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:23:49.57864+00:00
-- url     : https://prove2.me/theorems/f4653150-ce9d-45f5-82d1-db5be4bc3e3f
-- title:
--   Model Data: r eq
-- statement:
--   The reward decomposition, by definition: what `CSG.r` folds into one number.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L720-L722
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L720-L722

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.r_eq (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (s : Fin d.nStates) (a1 : Fin d.nAct1) (a2 : Fin d.nAct2) :
    d.toCsgQ.r s a1 a2 = (d.stateAt s).rew + (d.transAt s a1 a2).rew := by sorry
