-- Prove2me | Theorems.Thm_BKAR_Forest_standardInterp_mem_Icc
-- name    : BKAR.Forest.standardInterp_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:51.063886+00:00
-- url     : https://prove2.me/theorems/b900db67-4e3f-4401-b074-19d24a7fef2e
-- title:
--   Forest: standard Interp mem Icc
-- statement:
--   The Forest construction uses the standard Interp mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L171-L178
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L171-L178

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.standardInterp_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) (e : Edge V) :
    0 ≤ F.standardInterp u e ∧ F.standardInterp u e ≤ 1 := by sorry
