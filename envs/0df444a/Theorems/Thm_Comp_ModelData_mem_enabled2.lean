-- Prove2me | Theorems.Thm_Comp_ModelData_mem_enabled2
-- name    : Comp.ModelData.mem_enabled2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:37:33.887475+00:00
-- url     : https://prove2.me/theorems/ebf8c1f6-62b9-4931-91b0-4e793eede71f
-- title:
--   Model Data: mem enabled2
-- statement:
--   The Model Data construction uses the mem enabled2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L593-L595
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L593-L595

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.mem_enabled2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a2 : Fin d.nAct2) : a2 ∈ d.enabled2 hs s ↔ (a2 : ℕ) ∈ d.keys2 s := by sorry
