-- Prove2me | Theorems.Thm_Comp_ModelData_transAt_pad
-- name    : Comp.ModelData.transAt_pad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:51:40.381484+00:00
-- url     : https://prove2.me/theorems/e728c1bc-4950-41d4-bcea-ae0cb4ee76c5
-- title:
--   Model Data: trans At pad
-- statement:
--   **Padding invariance.** The transition a joint action denotes is the one its padded
--       representative denotes -- the padding map is a retraction onto the enabled set and the kernel
--       factors through it.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L432-L435
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L432-L435

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.transAt_pad (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s (d.pad1 s a1) (d.pad2 s a2) = d.transAt s a1 a2 := by sorry
