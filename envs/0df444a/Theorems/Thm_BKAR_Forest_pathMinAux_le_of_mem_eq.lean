-- Prove2me | Theorems.Thm_BKAR_Forest_pathMinAux_le_of_mem_eq
-- name    : BKAR.Forest.pathMinAux_le_of_mem_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:52.597187+00:00
-- url     : https://prove2.me/theorems/58102740-c381-5bee-9416-0aa125ff642c
-- title:
--   Forest: path Min Aux le of mem eq
-- statement:
--   The Forest construction uses the path Min Aux le of mem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L322-L338
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L322-L338

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pathMinAux_le_of_mem_eq (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {a : ℝ} (γ : List (Edge V)), e₀ ∈ γ →
      F.paramValue u e₀ = s → F.pathMinAux u a γ ≤ s
  := by sorry
