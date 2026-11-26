-- Prove2me | Theorems.Thm_BKAR_Forest_pathMin_le_of_mem_eq
-- name    : BKAR.Forest.pathMin_le_of_mem_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:00.086432+00:00
-- url     : https://prove2.me/theorems/bc62ef91-7126-4548-af29-deb901b2b32b
-- title:
--   Forest: path Min le of mem eq
-- statement:
--   The Forest construction uses the path Min le of mem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L340-L355
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L340-L355

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pathMin_le_of_mem_eq (F : Forest V) (u : F.EdgeParam → ℝ)
    {s : ℝ} {e₀ : Edge V} :
    ∀ {γ : List (Edge V)}, e₀ ∈ γ →
      F.paramValue u e₀ = s → F.pathMin u γ ≤ s
  := by sorry
