-- Prove2me | Theorems.Thm_Comp_ModelData_bTr_eq
-- name    : Comp.ModelData.bTr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:45:28.997927+00:00
-- url     : https://prove2.me/theorems/afe781bb-909a-41e9-9748-c6d6299dbd42
-- title:
--   Model Data: b Tr eq
-- statement:
--   **`bTr` is `bF` restricted to the enabled columns.** Unconditional: the `∃ a1 ∈ v1` is the
--       same on both sides, so only the support substitution is involved.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L281-L287
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L281-L287

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.bTr_eq [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) :
    d.bTr hs v1 x s = d.toCsgQ.bF v1 x s ∩ d.enabled2 hs s := by sorry
