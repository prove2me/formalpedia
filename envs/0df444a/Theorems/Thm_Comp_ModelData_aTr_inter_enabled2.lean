-- Prove2me | Theorems.Thm_Comp_ModelData_aTr_inter_enabled2
-- name    : Comp.ModelData.aTr_inter_enabled2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:53:52.105711+00:00
-- url     : https://prove2.me/theorems/01c91b8a-8d8a-48d7-87a3-c1e11a376317
-- title:
--   Model Data: a Tr inter enabled2
-- statement:
--   **`aTr` sees its `v2` only through the enabled columns.** No hypothesis needed, and the
--       contrast with `bTr_inter_enabled1` is the point: restricting a `∀` range that is already
--       restricted to `enabled2` is free, whereas restricting an `∃` witness set can lose a witness
--       unless pad-saturation guarantees its representative is also there.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L350-L365
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelDataQualitative.lean#L350-L365

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)

theorem Comp.ModelData.aTr_inter_enabled2 (hs : d.Shape) (s : Fin d.nStates) (v2 : Finset (Fin d.nAct2))
    (y : Finset (Fin d.nStates)) :
    d.aTr hs (v2 ∩ d.enabled2 hs s) y s = d.aTr hs v2 y s := by sorry
