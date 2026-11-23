-- Prove2me | Theorems.Thm_Comp_ModelData_enabled2_nonempty
-- name    : Comp.ModelData.enabled2_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:10:25.980053+00:00
-- url     : https://prove2.me/theorems/cd5f424b-1c09-4e36-b100-2d4651d97c07
-- title:
--   Model Data: enabled2 nonempty
-- statement:
--   The column player's.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L627-L631
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L627-L631

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.enabled2_nonempty (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    (d.enabled2 hs s).Nonempty := by sorry
