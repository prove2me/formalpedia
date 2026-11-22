-- Prove2me | Theorems.Thm_Comp_ModelData_padSat2_bF
-- name    : Comp.ModelData.padSat2_bF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:45:36.595174+00:00
-- url     : https://prove2.me/theorems/9216f80f-1737-40e8-b093-ec2004e92a92
-- title:
--   Model Data: pad Sat2 b F
-- statement:
--   **And `bF` does too**, for any `v1`. Same reason, on the other coordinate.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L237-L241
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L237-L241

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.padSat2_bF [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) : d.PadSat2 hs s (d.toCsgQ.bF v1 x s) := by sorry
