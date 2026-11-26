-- Prove2me | Theorems.Thm_BKAR_Forest_interpWithFill_mem_Icc
-- name    : BKAR.Forest.interpWithFill_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:18:30.284459+00:00
-- url     : https://prove2.me/theorems/9ed5c1db-415b-5f09-a5ab-f98aac8472f9
-- title:
--   Forest: interp With Fill mem Icc
-- statement:
--   The Forest construction uses the interp With Fill mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L180-L188
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L180-L188

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.interpWithFill_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (e : Edge V) :
    0 ≤ F.interpWithFill u t e ∧ F.interpWithFill u t e ≤ 1 := by sorry
