-- Prove2me | Theorems.Thm_Comp_ModelData_transAt_pad2
-- name    : Comp.ModelData.transAt_pad2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:52:42.54483+00:00
-- url     : https://prove2.me/theorems/5181f226-f2fe-40e4-be14-de58be63d251
-- title:
--   Model Data: trans At pad2
-- statement:
--   And the column action alone.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L665-L668
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L665-L668

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.transAt_pad2 (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s a1 (d.pad2 s a2) = d.transAt s a1 a2 := by sorry
