-- Prove2me | Theorems.Thm_Comp_ModelData_transAt_pad1
-- name    : Comp.ModelData.transAt_pad1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:52:40.127804+00:00
-- url     : https://prove2.me/theorems/7910d4d1-35ed-406c-845d-0b1345f5bc8d
-- title:
--   Model Data: trans At pad1
-- statement:
--   Padding the row action alone leaves the transition alone.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L659-L662
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L659-L662

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.transAt_pad1 (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s (d.pad1 s a1) a2 = d.transAt s a1 a2 := by sorry
