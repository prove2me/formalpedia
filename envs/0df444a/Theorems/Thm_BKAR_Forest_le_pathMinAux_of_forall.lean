-- Prove2me | Theorems.Thm_BKAR_Forest_le_pathMinAux_of_forall
-- name    : BKAR.Forest.le_pathMinAux_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:46.082048+00:00
-- url     : https://prove2.me/theorems/7a42d8f3-8d99-4d69-867f-44f9fc854490
-- title:
--   Forest: le path Min Aux of forall
-- statement:
--   The Forest construction uses the le path Min Aux of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L293-L308
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L293-L308

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.le_pathMinAux_of_forall (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} :
    ∀ {a : ℝ}, s ≤ a → ∀ γ : List (Edge V),
      (∀ e ∈ γ, s ≤ F.paramValue u e) → s ≤ F.pathMinAux u a γ
  := by sorry
