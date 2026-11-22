-- Prove2me | Theorems.Thm_Comp_ModelData_Stochastic_nonneg
-- name    : Comp.ModelData.Stochastic.nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:38:47.792752+00:00
-- url     : https://prove2.me/theorems/8d3f15ce-fb68-4825-960a-b5d6f3ca8bad
-- title:
--   Stochastic: nonneg
-- statement:
--   The Stochastic construction uses the nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L527-L528
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L527-L528

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.Stochastic.nonneg {d : ModelData} (h : d.Stochastic) : d.Nonneg := by sorry
