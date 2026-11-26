-- Prove2me | Theorems.Thm_BKAR_Forest_pathMinAux_eq_of_forall
-- name    : BKAR.Forest.pathMinAux_eq_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:37.657963+00:00
-- url     : https://prove2.me/theorems/166879cd-f27c-5cb1-8fd0-bba8a98af478
-- title:
--   Forest: path Min Aux eq of forall
-- statement:
--   The Forest construction uses the path Min Aux eq of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L225-L241
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L225-L241

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pathMinAux_eq_of_forall (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ) :
    ∀ {a b : ℝ}, a = b → ∀ γ : List (Edge V),
      (∀ e ∈ γ, F.paramValue u e = G.paramValue v e) →
        F.pathMinAux u a γ = G.pathMinAux v b γ
  := by sorry
