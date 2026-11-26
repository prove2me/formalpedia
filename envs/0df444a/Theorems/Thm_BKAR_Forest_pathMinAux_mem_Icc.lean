-- Prove2me | Theorems.Thm_BKAR_Forest_pathMinAux_mem_Icc
-- name    : BKAR.Forest.pathMinAux_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:22.589659+00:00
-- url     : https://prove2.me/theorems/c87b78bc-f9b2-4eca-9470-a73c375a9f23
-- title:
--   Forest: path Min Aux mem Icc
-- statement:
--   The Forest construction uses the path Min Aux mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L106-L116
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L106-L116

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pathMinAux_mem_Icc (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) :
    ∀ {a : ℝ}, 0 ≤ a ∧ a ≤ 1 → ∀ γ : List (Edge V),
      0 ≤ F.pathMinAux u a γ ∧ F.pathMinAux u a γ ≤ 1
  := by sorry
