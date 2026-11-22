-- Prove2me | Theorems.Thm_Comp_ModelData_pad2_idem
-- name    : Comp.ModelData.pad2_idem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:44:47.886705+00:00
-- url     : https://prove2.me/theorems/30088ef2-3266-4ff7-a8b1-b0f847a20a3c
-- title:
--   Model Data: pad2 idem
-- statement:
--   The column-side mirror.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L426-L427
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L426-L427

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.pad2_idem (d : ModelData) (s a2 : ℕ) : d.pad2 s (d.pad2 s a2) = d.pad2 s a2 := by sorry
