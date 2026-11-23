-- Prove2me | Theorems.Thm_Comp_ModelData_enabled1_nonempty
-- name    : Comp.ModelData.enabled1_nonempty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:10:16.265514+00:00
-- url     : https://prove2.me/theorems/24344a95-27cd-46e5-8bad-deaf05b9f52a
-- title:
--   Model Data: enabled1 nonempty
-- statement:
--   Neither enabled set is empty, since every state has a transition and it names an action.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L620-L624
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L620-L624

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.enabled1_nonempty (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    (d.enabled1 hs s).Nonempty := by sorry
