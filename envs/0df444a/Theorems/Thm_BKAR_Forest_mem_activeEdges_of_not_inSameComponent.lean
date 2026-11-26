-- Prove2me | Theorems.Thm_BKAR_Forest_mem_activeEdges_of_not_inSameComponent
-- name    : BKAR.Forest.mem_activeEdges_of_not_inSameComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:29.47619+00:00
-- url     : https://prove2.me/theorems/813c3826-2fbf-513a-ac94-a30f04f472e7
-- title:
--   Forest: mem active Edges of not in Same Component
-- statement:
--   The Forest construction uses the mem active Edges of not in Same Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L30-L33
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L30-L33

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mem_activeEdges_of_not_inSameComponent (F : Forest V) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    e ∈ F.activeEdges := by sorry
