-- Prove2me | Theorems.Thm_BKAR_Forest_emptyParam_unique
-- name    : BKAR.Forest.emptyParam_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:18.469224+00:00
-- url     : https://prove2.me/theorems/d2708cee-777d-4d40-945a-7f09e2388de5
-- title:
--   Forest: empty Param unique
-- statement:
--   The Forest construction uses the empty Param unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L50-L57
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L50-L57

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.emptyParam_unique (u : (Forest.empty V).EdgeParam → ℝ) :
    u = emptyParam := by sorry
