-- Prove2me | Theorems.Thm_Comp_ModelData_aTr_eq
-- name    : Comp.ModelData.aTr_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:46:15.807903+00:00
-- url     : https://prove2.me/theorems/9bd8294d-3911-4f49-b2ed-73c14a728eca
-- title:
--   Model Data: a Tr eq
-- statement:
--   **`aTr` is `aF` restricted to the enabled rows** -- and here pad-saturation earns its keep. The
--       inner `∀ a2` is narrowed to the enabled columns, which needs `v2` unable to tell a column
--       action from its representative: otherwise the dense form demands a support condition at a
--       disabled `a2` that the narrowed form never asks about.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L293-L307
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L293-L307

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.aTr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (s : Fin d.nStates) (v2 : Finset (Fin d.nAct2))
    (hv2 : d.PadSat2 hs s v2) (y : Finset (Fin d.nStates)) :
    d.aTr hs v2 y s = d.toCsgQ.aF v2 y s ∩ d.enabled1 hs s := by sorry
