-- Prove2me | Theorems.Thm_BKAR_Forest_empty_interpWithFill
-- name    : BKAR.Forest.empty_interpWithFill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:21.343018+00:00
-- url     : https://prove2.me/theorems/f8e94e71-acdb-48fa-97d9-1fa707709f91
-- title:
--   Forest: empty interp With Fill
-- statement:
--   The Forest construction uses the empty interp With Fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L199-L207
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L199-L207

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.empty_interpWithFill (u : (Forest.empty V).EdgeParam → ℝ)
    (t : ℝ) :
    (Forest.empty V).interpWithFill u t = constantConfig t := by sorry
