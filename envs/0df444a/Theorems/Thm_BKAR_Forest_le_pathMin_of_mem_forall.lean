-- Prove2me | Theorems.Thm_BKAR_Forest_le_pathMin_of_mem_forall
-- name    : BKAR.Forest.le_pathMin_of_mem_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:52.847797+00:00
-- url     : https://prove2.me/theorems/e75a4359-206c-4cb4-97cc-0c85b03da4b0
-- title:
--   Forest: le path Min of mem forall
-- statement:
--   The Forest construction uses the le path Min of mem forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L310-L320
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L310-L320

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.le_pathMin_of_mem_forall (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {γ : List (Edge V)}, e₀ ∈ γ →
      (∀ e ∈ γ, s ≤ F.paramValue u e) → s ≤ F.pathMin u γ
  := by sorry
