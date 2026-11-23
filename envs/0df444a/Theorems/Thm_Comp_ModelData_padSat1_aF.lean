-- Prove2me | Theorems.Thm_Comp_ModelData_padSat1_aF
-- name    : Comp.ModelData.padSat1_aF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:45:44.102975+00:00
-- url     : https://prove2.me/theorems/6e4a36f9-246a-4204-9ffe-1e721e9e0d46
-- title:
--   Model Data: pad Sat1 a F
-- statement:
--   **`aF` produces pad-saturated sets**, for any `v2` at all. Only the support term mentions the
--       row action, and the support does not see its padding.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L230-L234
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L230-L234

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.padSat1_aF [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v2 : Finset (Fin d.nAct2)) (y : Finset (Fin d.nStates))
    (s : Fin d.nStates) : d.PadSat1 hs s (d.toCsgQ.aF v2 y s) := by sorry
