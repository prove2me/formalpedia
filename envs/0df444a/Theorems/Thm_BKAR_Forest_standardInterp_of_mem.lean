-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_of_mem
-- name    : BKAR.Forest.standardInterp_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:18:18.552856+00:00
-- url     : https://prove2.me/theorems/ac36b0b3-3350-44bd-9ebe-46c447043f3b
-- title:
--   Forest: standard Interp of mem
-- statement:
--   The Forest construction uses the standard Interp of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L159-L163
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L159-L163

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.standardInterp_of_mem (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.standardInterp u e = u ⟨e, he⟩ := by sorry
