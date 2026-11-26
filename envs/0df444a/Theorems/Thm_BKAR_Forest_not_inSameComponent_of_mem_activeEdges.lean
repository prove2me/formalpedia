-- Prove2me | Theorems.Thm_BKAR_Forest_not_inSameComponent_of_mem_activeEdges
-- name    : BKAR.Forest.not_inSameComponent_of_mem_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:04.4089+00:00
-- url     : https://prove2.me/theorems/318b9823-849a-58d9-867f-a9c0287e2010
-- title:
--   Forest: not in Same Component of mem active Edges
-- statement:
--   The Forest construction uses the not in Same Component of mem active Edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L35-L38
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L35-L38

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.not_inSameComponent_of_mem_activeEdges (F : Forest V) {e : Edge V}
    (he : e ∈ F.activeEdges) :
    ¬ F.inSameComponent e.left e.right := by sorry
