-- Prove2me | Theorems.Thm_BKAR_Forest_pathMin_eq_of_forall
-- name    : BKAR.Forest.pathMin_eq_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:25.228326+00:00
-- url     : https://prove2.me/theorems/e7ab9c9e-cec6-488f-93a5-0d7b726687dd
-- title:
--   Forest: path Min eq of forall
-- statement:
--   The Forest construction uses the path Min eq of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L243-L258
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L243-L258

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.pathMin_eq_of_forall (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ) :
    ∀ γ : List (Edge V),
      (∀ e ∈ γ, F.paramValue u e = G.paramValue v e) →
        F.pathMin u γ = G.pathMin v γ
  := by sorry
