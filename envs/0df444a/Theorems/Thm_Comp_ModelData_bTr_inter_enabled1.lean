-- Prove2me | Theorems.Thm_Comp_ModelData_bTr_inter_enabled1
-- name    : Comp.ModelData.bTr_inter_enabled1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:42:21.599166+00:00
-- url     : https://prove2.me/theorems/b2fcbd18-f0bc-4491-9937-59d78b18d96d
-- title:
--   Model Data: b Tr inter enabled1
-- statement:
--   **`bTr` sees its argument only through its enabled part**, which is what keeps the chain
--       narrow: the row-action sets the iteration carries are subsets of `enabled1`, while the dense
--       chain's are pad-saturated. Needs pad-saturation, since a disabled row action in `v1` mirrors
--       its representative and pad-saturation is the guarantee that the representative is there too.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L313-L323
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L313-L323

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.bTr_inter_enabled1 (hs : d.Shape) (s : Fin d.nStates) (v1 : Finset (Fin d.nAct1))
    (hv1 : d.PadSat1 hs s v1) (x : Finset (Fin d.nStates)) :
    d.bTr hs (v1 ∩ d.enabled1 hs s) x s = d.bTr hs v1 x s := by sorry
