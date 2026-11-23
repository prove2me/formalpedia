-- Prove2me | Theorems.Thm_Comp_ModelData_pad1_idem
-- name    : Comp.ModelData.pad1_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:44:36.960602+00:00
-- url     : https://prove2.me/theorems/3bded34c-dca2-43f1-abd4-fe7386f6a50b
-- title:
--   Model Data: pad1 idem
-- statement:
--   Padding twice is padding once -- it lands in the enabled set, where it is the identity.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L422-L423
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L422-L423

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.pad1_idem (d : ModelData) (s a1 : ℕ) : d.pad1 s (d.pad1 s a1) = d.pad1 s a1 := by sorry
