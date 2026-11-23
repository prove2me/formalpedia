-- Prove2me | Theorems.Thm_Comp_ModelData_padSat1_lStepF_iterate
-- name    : Comp.ModelData.padSat1_lStepF_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:54:05.690803+00:00
-- url     : https://prove2.me/theorems/5f10c2f0-f215-492d-ba87-31f53f988b15
-- title:
--   Model Data: pad Sat1 l Step F iterate
-- statement:
--   Every stage of the dense climb is pad-saturated -- the invariant the correspondence needs,
--       and it costs nothing because each stage is an `aF`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L383-L392
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L383-L392

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.padSat1_lStepF_iterate [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (x y : Finset (Fin d.nStates)) (s : Fin d.nStates) (k : ℕ) :
    d.PadSat1 hs s ((d.toCsgQ.lStepF x y s)^[k] ∅) := by sorry
