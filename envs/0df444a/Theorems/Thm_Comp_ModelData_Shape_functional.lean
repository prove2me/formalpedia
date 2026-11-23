-- Prove2me | Theorems.Thm_Comp_ModelData_Shape_functional
-- name    : Comp.ModelData.Shape.functional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:10:02.459093+00:00
-- url     : https://prove2.me/theorems/3bd20905-8906-408e-98a5-0cccf94de8fd
-- title:
--   Shape: functional
-- statement:
--   The Shape construction uses the functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L496-L496
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L496-L496

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.Shape.functional {d : ModelData} (hs : d.Shape) : d.Functional := by sorry
