-- Prove2me | Theorems.Thm_Comp_ModelData_pad2_eq_self
-- name    : Comp.ModelData.pad2_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:44:25.925212+00:00
-- url     : https://prove2.me/theorems/41b0c97e-6a6a-41b0-8da7-97ad7aecf12e
-- title:
--   Model Data: pad2 eq self
-- statement:
--   The column-side mirror.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L415-L419
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L415-L419

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.pad2_eq_self (d : ModelData) {s a2 : ℕ} (h : a2 ∈ d.keys2 s) :
    d.pad2 s a2 = a2 := by sorry
