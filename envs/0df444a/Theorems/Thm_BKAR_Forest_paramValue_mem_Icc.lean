-- Prove2me | Theorems.Thm_BKAR_Forest_paramValue_mem_Icc
-- name    : BKAR.Forest.paramValue_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:16.04322+00:00
-- url     : https://prove2.me/theorems/6120b229-481e-5f64-b25b-ff3a6a3fd197
-- title:
--   Forest: param Value mem Icc
-- statement:
--   The Forest construction uses the param Value mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L97-L104
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L97-L104

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramValue_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) (e : Edge V) :
    0 ≤ F.paramValue u e ∧ F.paramValue u e ≤ 1 := by sorry
